import Jsp000404.SevenLowerCheckCompose
import Jsp000404.SevenLowerFixedCutGroup00
import Jsp000404.SevenLowerFixedCutGroup01
import Jsp000404.SevenLowerFixedCutGroup02
import Jsp000404.SevenLowerFixedCutGroup03
import Jsp000404.SevenLowerFixedCutGroup04
import Jsp000404.SevenLowerFixedCutGroup05
import Jsp000404.SevenLowerFixedCutGroup06
import Jsp000404.SevenLowerFixedCutGroup07
import Jsp000404.SevenLowerFixedCutGroup08
import Jsp000404.SevenLowerFixedCutGroup09
import Jsp000404.SevenLowerFixedCutGroup10
import Jsp000404.SevenLowerFixedCutGroup11
import Jsp000404.SevenLowerFixedCutGroup12
import Jsp000404.SevenLowerFixedCutGroup13
import Mathlib.Tactic.FinCases

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchComposedRootCheck
open SevenLowerReplay
private theorem prefix375_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context375 10426 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context375 10426 3 10350 10425
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup13.cuts_checked 2)
  · exact (SevenLowerFixedCutGroup13.cuts_checked 3)

private theorem prefix374_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context374 10511 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context374 10511 6 10426 10510
  · rfl
  · decide
  · exact prefix375_checked
  · exact (SevenLowerFixedCutGroup13.cuts_checked 4)

private theorem prefix373_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context373 10651 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context373 10651 8 10511 10650
  · rfl
  · decide
  · exact prefix374_checked
  · exact (SevenLowerFixedCutGroup13.cuts_checked 5)

private theorem prefix372_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context372 10810 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context372 10810 9 10651 10809
  · rfl
  · decide
  · exact prefix373_checked
  · exact (SevenLowerFixedCutGroup13.cuts_checked 6)

private theorem prefix368_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context368 10191 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context368 10191 2 10104 10190
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup12.cuts_checked 11)
  · exact (SevenLowerFixedCutGroup13.cuts_checked 0)

private theorem prefix367_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context367 10281 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context367 10281 5 10191 10280
  · rfl
  · decide
  · exact prefix368_checked
  · exact (SevenLowerFixedCutGroup13.cuts_checked 1)

private theorem prefix362_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context362 9793 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context362 9793 3 9729 9792
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup12.cuts_checked 7)
  · exact (SevenLowerFixedCutGroup12.cuts_checked 8)

private theorem prefix361_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context361 9916 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context361 9916 6 9793 9915
  · rfl
  · decide
  · exact prefix362_checked
  · exact (SevenLowerFixedCutGroup12.cuts_checked 9)

private theorem prefix360_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context360 10033 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context360 10033 9 9916 10032
  · rfl
  · decide
  · exact prefix361_checked
  · exact (SevenLowerFixedCutGroup12.cuts_checked 10)

private theorem prefix357_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context357 9663 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context357 9663 2 9592 9662
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup12.cuts_checked 5)
  · exact (SevenLowerFixedCutGroup12.cuts_checked 6)

private theorem prefix353_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context353 9459 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context353 9459 3 9407 9458
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup12.cuts_checked 2)
  · exact (SevenLowerFixedCutGroup12.cuts_checked 3)

private theorem prefix352_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context352 9526 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context352 9526 9 9459 9525
  · rfl
  · decide
  · exact prefix353_checked
  · exact (SevenLowerFixedCutGroup12.cuts_checked 4)

private theorem prefix348_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context348 9298 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context348 9298 9 9238 9297
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup11.cuts_checked 14)
  · exact (SevenLowerFixedCutGroup12.cuts_checked 0)

private theorem prefix347_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context347 9360 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context347 9360 3 9298 9359
  · rfl
  · decide
  · exact prefix348_checked
  · exact (SevenLowerFixedCutGroup12.cuts_checked 1)

private theorem prefix346_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context346 9527 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context346 9527 2 9360 9526
  · rfl
  · decide
  · exact prefix347_checked
  · exact prefix352_checked

private theorem prefix345_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context345 9664 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context345 9664 6 9527 9663
  · rfl
  · decide
  · exact prefix346_checked
  · exact prefix357_checked

private theorem prefix344_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context344 10034 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context344 10034 5 9664 10033
  · rfl
  · decide
  · exact prefix345_checked
  · exact prefix360_checked

private theorem prefix343_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context343 10282 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context343 10282 8 10034 10281
  · rfl
  · decide
  · exact prefix344_checked
  · exact prefix367_checked

private theorem prefix342_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 24 SevenLowerFixedCutContexts.context342 10811 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context342 10811 7 10282 10810
  · rfl
  · decide
  · exact prefix343_checked
  · exact prefix372_checked

private theorem prefix339_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context339 9205 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context339 9205 1 9130 9204
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup11.cuts_checked 12)
  · exact (SevenLowerFixedCutGroup11.cuts_checked 13)

private theorem prefix336_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context336 9079 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context336 9079 1 9013 9078
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup11.cuts_checked 10)
  · exact (SevenLowerFixedCutGroup11.cuts_checked 11)

private theorem prefix332_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context332 8873 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context332 8873 3 8813 8872
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup11.cuts_checked 7)
  · exact (SevenLowerFixedCutGroup11.cuts_checked 8)

private theorem prefix331_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context331 8946 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context331 8946 8 8873 8945
  · rfl
  · decide
  · exact prefix332_checked
  · exact (SevenLowerFixedCutGroup11.cuts_checked 9)

private theorem prefix327_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context327 8697 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context327 8697 8 8637 8696
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup11.cuts_checked 4)
  · exact (SevenLowerFixedCutGroup11.cuts_checked 5)

private theorem prefix326_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context326 8759 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context326 8759 3 8697 8758
  · rfl
  · decide
  · exact prefix327_checked
  · exact (SevenLowerFixedCutGroup11.cuts_checked 6)

private theorem prefix325_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context325 8947 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context325 8947 1 8759 8946
  · rfl
  · decide
  · exact prefix326_checked
  · exact prefix331_checked

private theorem prefix324_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context324 9080 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context324 9080 6 8947 9079
  · rfl
  · decide
  · exact prefix325_checked
  · exact prefix336_checked

private theorem prefix323_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context323 9206 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context323 9206 9 9080 9205
  · rfl
  · decide
  · exact prefix324_checked
  · exact prefix339_checked

private theorem prefix319_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context319 8523 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context319 8523 2 8459 8522
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup11.cuts_checked 1)
  · exact (SevenLowerFixedCutGroup11.cuts_checked 2)

private theorem prefix318_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context318 8601 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context318 8601 7 8523 8600
  · rfl
  · decide
  · exact prefix319_checked
  · exact (SevenLowerFixedCutGroup11.cuts_checked 3)

private theorem prefix314_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context314 8345 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context314 8345 7 8285 8344
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup10.cuts_checked 8)
  · exact (SevenLowerFixedCutGroup10.cuts_checked 9)

private theorem prefix313_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context313 8406 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context313 8406 2 8345 8405
  · rfl
  · decide
  · exact prefix314_checked
  · exact (SevenLowerFixedCutGroup11.cuts_checked 0)

private theorem prefix312_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context312 8602 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context312 8602 1 8406 8601
  · rfl
  · decide
  · exact prefix313_checked
  · exact prefix318_checked

private theorem prefix307_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context307 8022 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context307 8022 3 7967 8021
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup10.cuts_checked 4)
  · exact (SevenLowerFixedCutGroup10.cuts_checked 5)

private theorem prefix306_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context306 8105 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context306 8105 8 8022 8104
  · rfl
  · decide
  · exact prefix307_checked
  · exact (SevenLowerFixedCutGroup10.cuts_checked 6)

private theorem prefix305_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context305 8249 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context305 8249 9 8105 8248
  · rfl
  · decide
  · exact prefix306_checked
  · exact (SevenLowerFixedCutGroup10.cuts_checked 7)

private theorem prefix302_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context302 7917 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context302 7917 2 7853 7916
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup10.cuts_checked 2)
  · exact (SevenLowerFixedCutGroup10.cuts_checked 3)

private theorem prefix298_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context298 7706 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context298 7706 3 7562 7705
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup09.cuts_checked 7)
  · exact (SevenLowerFixedCutGroup10.cuts_checked 0)

private theorem prefix297_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context297 7802 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context297 7802 9 7706 7801
  · rfl
  · decide
  · exact prefix298_checked
  · exact (SevenLowerFixedCutGroup10.cuts_checked 1)

private theorem prefix293_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context293 7351 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context293 7351 9 7250 7350
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup09.cuts_checked 4)
  · exact (SevenLowerFixedCutGroup09.cuts_checked 5)

private theorem prefix292_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context292 7462 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context292 7462 3 7351 7461
  · rfl
  · decide
  · exact prefix293_checked
  · exact (SevenLowerFixedCutGroup09.cuts_checked 6)

private theorem prefix291_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context291 7803 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context291 7803 2 7462 7802
  · rfl
  · decide
  · exact prefix292_checked
  · exact prefix297_checked

private theorem prefix290_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context290 7918 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context290 7918 8 7803 7917
  · rfl
  · decide
  · exact prefix291_checked
  · exact prefix302_checked

private theorem prefix289_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context289 8250 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context289 8250 7 7918 8249
  · rfl
  · decide
  · exact prefix290_checked
  · exact prefix305_checked

private theorem prefix284_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context284 6964 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context284 6964 8 6842 6963
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup09.cuts_checked 0)
  · exact (SevenLowerFixedCutGroup09.cuts_checked 1)

private theorem prefix283_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context283 7114 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context283 7114 3 6964 7113
  · rfl
  · decide
  · exact prefix284_checked
  · exact (SevenLowerFixedCutGroup09.cuts_checked 2)

private theorem prefix282_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context282 7179 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context282 7179 9 7114 7178
  · rfl
  · decide
  · exact prefix283_checked
  · exact (SevenLowerFixedCutGroup09.cuts_checked 3)

private theorem prefix279_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context279 6775 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context279 6775 7 6589 6774
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup08.cuts_checked 6)
  · exact (SevenLowerFixedCutGroup08.cuts_checked 7)

private theorem prefix275_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context275 6380 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context275 6380 8 6288 6379
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup08.cuts_checked 3)
  · exact (SevenLowerFixedCutGroup08.cuts_checked 4)

private theorem prefix274_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context274 6523 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context274 6523 9 6380 6522
  · rfl
  · decide
  · exact prefix275_checked
  · exact (SevenLowerFixedCutGroup08.cuts_checked 5)

private theorem prefix270_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context270 6188 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context270 6188 9 6115 6187
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup08.cuts_checked 0)
  · exact (SevenLowerFixedCutGroup08.cuts_checked 1)

private theorem prefix269_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context269 6228 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context269 6228 8 6188 6227
  · rfl
  · decide
  · exact prefix270_checked
  · exact (SevenLowerFixedCutGroup08.cuts_checked 2)

private theorem prefix268_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context268 6524 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context268 6524 7 6228 6523
  · rfl
  · decide
  · exact prefix269_checked
  · exact prefix274_checked

private theorem prefix267_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context267 6776 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context267 6776 3 6524 6775
  · rfl
  · decide
  · exact prefix268_checked
  · exact prefix279_checked

private theorem prefix266_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context266 7180 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context266 7180 2 6776 7179
  · rfl
  · decide
  · exact prefix267_checked
  · exact prefix282_checked

private theorem prefix265_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context265 8251 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context265 8251 1 7180 8250
  · rfl
  · decide
  · exact prefix266_checked
  · exact prefix289_checked

private theorem prefix264_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context264 8603 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context264 8603 6 8251 8602
  · rfl
  · decide
  · exact prefix265_checked
  · exact prefix312_checked

private theorem prefix263_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 24 SevenLowerFixedCutContexts.context263 9207 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context263 9207 5 8603 9206
  · rfl
  · decide
  · exact prefix264_checked
  · exact prefix323_checked

private theorem prefix262_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 25 SevenLowerFixedCutContexts.context262 10812 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 24 SevenLowerFixedCutContexts.context262 10812 4 9207 10811
  · rfl
  · decide
  · exact prefix263_checked
  · exact prefix342_checked

private theorem prefix256_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context256 5875 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context256 5875 6 5823 5874
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup07.cuts_checked 8)
  · exact (SevenLowerFixedCutGroup07.cuts_checked 9)

private theorem prefix255_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context255 5922 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context255 5922 3 5875 5921
  · rfl
  · decide
  · exact prefix256_checked
  · exact (SevenLowerFixedCutGroup07.cuts_checked 10)

private theorem prefix254_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context254 5985 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context254 5985 8 5922 5984
  · rfl
  · decide
  · exact prefix255_checked
  · exact (SevenLowerFixedCutGroup07.cuts_checked 11)

private theorem prefix253_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context253 6031 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context253 6031 9 5985 6030
  · rfl
  · decide
  · exact prefix254_checked
  · exact (SevenLowerFixedCutGroup07.cuts_checked 12)

private theorem prefix249_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context249 5743 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context249 5743 5 5694 5742
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup07.cuts_checked 5)
  · exact (SevenLowerFixedCutGroup07.cuts_checked 6)

private theorem prefix248_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context248 5794 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context248 5794 2 5743 5793
  · rfl
  · decide
  · exact prefix249_checked
  · exact (SevenLowerFixedCutGroup07.cuts_checked 7)

private theorem prefix243_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context243 5503 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context243 5503 6 5385 5502
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup07.cuts_checked 1)
  · exact (SevenLowerFixedCutGroup07.cuts_checked 2)

private theorem prefix242_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context242 5615 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context242 5615 3 5503 5614
  · rfl
  · decide
  · exact prefix243_checked
  · exact (SevenLowerFixedCutGroup07.cuts_checked 3)

private theorem prefix241_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context241 5665 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context241 5665 9 5615 5664
  · rfl
  · decide
  · exact prefix242_checked
  · exact (SevenLowerFixedCutGroup07.cuts_checked 4)

private theorem prefix238_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context238 5334 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context238 5334 5 5197 5333
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup06.cuts_checked 29)
  · exact (SevenLowerFixedCutGroup07.cuts_checked 0)

private theorem prefix234_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context234 5027 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context234 5027 6 4945 5026
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup06.cuts_checked 26)
  · exact (SevenLowerFixedCutGroup06.cuts_checked 27)

private theorem prefix233_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context233 5146 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context233 5146 9 5027 5145
  · rfl
  · decide
  · exact prefix234_checked
  · exact (SevenLowerFixedCutGroup06.cuts_checked 28)

private theorem prefix229_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context229 4853 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context229 4853 9 4794 4852
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup06.cuts_checked 23)
  · exact (SevenLowerFixedCutGroup06.cuts_checked 24)

private theorem prefix228_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context228 4892 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context228 4892 6 4853 4891
  · rfl
  · decide
  · exact prefix229_checked
  · exact (SevenLowerFixedCutGroup06.cuts_checked 25)

private theorem prefix227_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context227 5147 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context227 5147 5 4892 5146
  · rfl
  · decide
  · exact prefix228_checked
  · exact prefix233_checked

private theorem prefix226_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context226 5335 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context226 5335 3 5147 5334
  · rfl
  · decide
  · exact prefix227_checked
  · exact prefix238_checked

private theorem prefix225_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context225 5666 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context225 5666 2 5335 5665
  · rfl
  · decide
  · exact prefix226_checked
  · exact prefix241_checked

private theorem prefix224_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context224 5795 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context224 5795 8 5666 5794
  · rfl
  · decide
  · exact prefix225_checked
  · exact prefix248_checked

private theorem prefix223_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 24 SevenLowerFixedCutContexts.context223 6032 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context223 6032 7 5795 6031
  · rfl
  · decide
  · exact prefix224_checked
  · exact prefix253_checked

private theorem prefix220_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context220 4720 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context220 4720 4 4666 4719
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup06.cuts_checked 21)
  · exact (SevenLowerFixedCutGroup06.cuts_checked 22)

private theorem prefix198_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context198 4637 = true := by
  apply SevenLowerCheckCompose.check_heavy_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context198 4637 (![4534, 4535, 4536, 4537, 4538, 4539, 4540, 4541, 4581, 4604, 4626, 4627, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636])
  · rfl
  · decide
  · intro p
    fin_cases p
    · exact (SevenLowerFixedCutGroup06.cuts_checked 0)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 1)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 2)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 3)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 4)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 5)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 6)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 7)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 8)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 9)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 10)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 11)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 12)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 13)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 14)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 15)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 16)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 17)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 18)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 19)
    · exact (SevenLowerFixedCutGroup06.cuts_checked 20)

private theorem prefix196_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context196 4638 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context196 4638 4 4475 4637
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup05.cuts_checked 27)
  · exact prefix198_checked

private theorem prefix192_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context192 4275 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context192 4275 6 4193 4274
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup05.cuts_checked 24)
  · exact (SevenLowerFixedCutGroup05.cuts_checked 25)

private theorem prefix191_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context191 4424 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context191 4424 8 4275 4423
  · rfl
  · decide
  · exact prefix192_checked
  · exact (SevenLowerFixedCutGroup05.cuts_checked 26)

private theorem prefix187_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context187 4100 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context187 4100 8 4040 4099
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup05.cuts_checked 21)
  · exact (SevenLowerFixedCutGroup05.cuts_checked 22)

private theorem prefix186_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context186 4139 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context186 4139 6 4100 4138
  · rfl
  · decide
  · exact prefix187_checked
  · exact (SevenLowerFixedCutGroup05.cuts_checked 23)

private theorem prefix185_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context185 4425 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context185 4425 4 4139 4424
  · rfl
  · decide
  · exact prefix186_checked
  · exact prefix191_checked

private theorem prefix184_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context184 4639 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context184 4639 3 4425 4638
  · rfl
  · decide
  · exact prefix185_checked
  · exact prefix196_checked

private theorem prefix183_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context183 4721 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context183 4721 9 4639 4720
  · rfl
  · decide
  · exact prefix184_checked
  · exact prefix220_checked

private theorem prefix161_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context161 3965 = true := by
  apply SevenLowerCheckCompose.check_heavy_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context161 3965 (![3869, 3870, 3871, 3872, 3873, 3874, 3875, 3915, 3942, 3943, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964])
  · rfl
  · decide
  · intro p
    fin_cases p
    · exact (SevenLowerFixedCutGroup05.cuts_checked 0)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 1)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 2)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 3)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 4)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 5)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 6)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 7)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 8)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 9)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 10)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 11)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 12)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 13)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 14)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 15)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 16)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 17)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 18)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 19)
    · exact (SevenLowerFixedCutGroup05.cuts_checked 20)

private theorem prefix158_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context158 3808 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context158 3808 5 3724 3807
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup04.cuts_checked 27)
  · exact (SevenLowerFixedCutGroup04.cuts_checked 28)

private theorem prefix157_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context157 3966 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context157 3966 7 3808 3965
  · rfl
  · decide
  · exact prefix158_checked
  · exact prefix161_checked

private theorem prefix153_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context153 3631 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context153 3631 7 3571 3630
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup04.cuts_checked 24)
  · exact (SevenLowerFixedCutGroup04.cuts_checked 25)

private theorem prefix152_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context152 3670 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context152 3670 5 3631 3669
  · rfl
  · decide
  · exact prefix153_checked
  · exact (SevenLowerFixedCutGroup04.cuts_checked 26)

private theorem prefix151_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context151 3967 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context151 3967 4 3670 3966
  · rfl
  · decide
  · exact prefix152_checked
  · exact prefix157_checked

private theorem prefix129_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context129 3496 = true := by
  apply SevenLowerCheckCompose.check_heavy_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context129 3496 (![3346, 3376, 3377, 3378, 3379, 3380, 3434, 3467, 3468, 3469, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495])
  · rfl
  · decide
  · intro p
    fin_cases p
    · exact (SevenLowerFixedCutGroup04.cuts_checked 3)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 4)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 5)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 6)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 7)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 8)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 9)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 10)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 11)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 12)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 13)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 14)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 15)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 16)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 17)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 18)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 19)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 20)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 21)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 22)
    · exact (SevenLowerFixedCutGroup04.cuts_checked 23)

private theorem prefix125_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context125 3171 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context125 3171 6 3118 3170
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup04.cuts_checked 0)
  · exact (SevenLowerFixedCutGroup04.cuts_checked 1)

private theorem prefix124_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context124 3290 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context124 3290 8 3171 3289
  · rfl
  · decide
  · exact prefix125_checked
  · exact (SevenLowerFixedCutGroup04.cuts_checked 2)

private theorem prefix123_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context123 3497 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context123 3497 9 3290 3496
  · rfl
  · decide
  · exact prefix124_checked
  · exact prefix129_checked

private theorem prefix120_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context120 3052 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context120 3052 5 3007 3051
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup03.cuts_checked 26)
  · exact (SevenLowerFixedCutGroup03.cuts_checked 27)

private theorem prefix097_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context097 2834 = true := by
  apply SevenLowerCheckCompose.check_heavy_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 15 SevenLowerFixedCutContexts.context097 2834 (![2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2663, 2752, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833])
  · rfl
  · decide
  · intro p
    fin_cases p
    · exact (SevenLowerFixedCutGroup03.cuts_checked 4)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 5)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 6)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 7)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 8)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 9)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 10)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 11)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 12)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 13)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 14)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 15)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 16)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 17)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 18)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 19)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 20)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 21)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 22)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 23)
    · exact (SevenLowerFixedCutGroup03.cuts_checked 24)

private theorem prefix095_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context095 2835 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context095 2835 6 2619 2834
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup03.cuts_checked 3)
  · exact prefix097_checked

private theorem prefix094_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context094 2956 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context094 2956 9 2835 2955
  · rfl
  · decide
  · exact prefix095_checked
  · exact (SevenLowerFixedCutGroup03.cuts_checked 25)

private theorem prefix090_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context090 2432 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context090 2432 9 2337 2431
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup03.cuts_checked 0)
  · exact (SevenLowerFixedCutGroup03.cuts_checked 1)

private theorem prefix089_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context089 2516 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context089 2516 6 2432 2515
  · rfl
  · decide
  · exact prefix090_checked
  · exact (SevenLowerFixedCutGroup03.cuts_checked 2)

private theorem prefix088_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context088 2957 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context088 2957 5 2516 2956
  · rfl
  · decide
  · exact prefix089_checked
  · exact prefix094_checked

private theorem prefix087_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context087 3053 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context087 3053 8 2957 3052
  · rfl
  · decide
  · exact prefix088_checked
  · exact prefix120_checked

private theorem prefix086_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context086 3498 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context086 3498 7 3053 3497
  · rfl
  · decide
  · exact prefix087_checked
  · exact prefix123_checked

private theorem prefix081_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context081 2151 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context081 2151 8 2072 2150
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup02.cuts_checked 24)
  · exact (SevenLowerFixedCutGroup02.cuts_checked 25)

private theorem prefix080_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context080 2213 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context080 2213 6 2151 2212
  · rfl
  · decide
  · exact prefix081_checked
  · exact (SevenLowerFixedCutGroup02.cuts_checked 26)

private theorem prefix079_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context079 2249 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context079 2249 9 2213 2248
  · rfl
  · decide
  · exact prefix080_checked
  · exact (SevenLowerFixedCutGroup02.cuts_checked 27)

private theorem prefix076_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context076 2004 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context076 2004 7 1930 2003
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup02.cuts_checked 22)
  · exact (SevenLowerFixedCutGroup02.cuts_checked 23)

private theorem prefix054_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context054 1865 = true := by
  apply SevenLowerCheckCompose.check_heavy_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context054 1865 (![1673, 1674, 1738, 1739, 1740, 1741, 1742, 1783, 1808, 1809, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864])
  · rfl
  · decide
  · intro p
    fin_cases p
    · exact (SevenLowerFixedCutGroup02.cuts_checked 1)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 2)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 3)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 4)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 5)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 6)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 7)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 8)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 9)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 10)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 11)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 12)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 13)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 14)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 15)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 16)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 17)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 18)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 19)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 20)
    · exact (SevenLowerFixedCutGroup02.cuts_checked 21)

private theorem prefix051_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context051 1670 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context051 1670 8 1531 1669
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup01.cuts_checked 18)
  · exact (SevenLowerFixedCutGroup02.cuts_checked 0)

private theorem prefix050_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context050 1866 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context050 1866 9 1670 1865
  · rfl
  · decide
  · exact prefix051_checked
  · exact prefix054_checked

private theorem prefix028_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 12 SevenLowerFixedCutContexts.context028 785 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 11 SevenLowerFixedCutContexts.context028 785 11 589 784
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup00.cuts_checked 10)
  · exact (SevenLowerFixedCutGroup00.cuts_checked 11)

private theorem prefix027_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 13 SevenLowerFixedCutContexts.context027 820 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 12 SevenLowerFixedCutContexts.context027 820 14 785 819
  · rfl
  · decide
  · exact prefix028_checked
  · exact (SevenLowerFixedCutGroup00.cuts_checked 12)

private theorem prefix026_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 14 SevenLowerFixedCutContexts.context026 1000 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 13 SevenLowerFixedCutContexts.context026 1000 13 820 999
  · rfl
  · decide
  · exact prefix027_checked
  · exact (SevenLowerFixedCutGroup01.cuts_checked 0)

private theorem prefix021_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 11 SevenLowerFixedCutContexts.context021 442 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 10 SevenLowerFixedCutContexts.context021 442 15 352 441
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup00.cuts_checked 6)
  · exact (SevenLowerFixedCutGroup00.cuts_checked 7)

private theorem prefix019_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 12 SevenLowerFixedCutContexts.context019 443 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 11 SevenLowerFixedCutContexts.context019 443 13 252 442
  · rfl
  · decide
  · exact (SevenLowerFixedCutGroup00.cuts_checked 5)
  · exact prefix021_checked

private theorem prefix018_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 13 SevenLowerFixedCutContexts.context018 476 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 12 SevenLowerFixedCutContexts.context018 476 12 443 475
  · rfl
  · decide
  · exact prefix019_checked
  · exact (SevenLowerFixedCutGroup00.cuts_checked 8)

private theorem prefix017_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 14 SevenLowerFixedCutContexts.context017 539 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 13 SevenLowerFixedCutContexts.context017 539 11 476 538
  · rfl
  · decide
  · exact prefix018_checked
  · exact (SevenLowerFixedCutGroup00.cuts_checked 9)

private theorem prefix016_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 15 SevenLowerFixedCutContexts.context016 1001 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 14 SevenLowerFixedCutContexts.context016 1001 10 539 1000
  · rfl
  · decide
  · exact prefix017_checked
  · exact prefix026_checked

private theorem prefix010_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context010 1155 = true := by
  apply SevenLowerCheckCompose.check_heavy_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 15 SevenLowerFixedCutContexts.context010 1155 (![2, 3, 4, 5, 115, 1001, 1002, 1003, 1004, 1041, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154])
  · rfl
  · decide
  · intro p
    fin_cases p
    · exact (SevenLowerFixedCutGroup00.cuts_checked 0)
    · exact (SevenLowerFixedCutGroup00.cuts_checked 1)
    · exact (SevenLowerFixedCutGroup00.cuts_checked 2)
    · exact (SevenLowerFixedCutGroup00.cuts_checked 3)
    · exact (SevenLowerFixedCutGroup00.cuts_checked 4)
    · exact prefix016_checked
    · exact (SevenLowerFixedCutGroup01.cuts_checked 1)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 2)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 3)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 4)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 5)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 6)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 7)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 8)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 9)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 10)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 11)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 12)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 13)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 14)
    · exact (SevenLowerFixedCutGroup01.cuts_checked 15)

private theorem prefix009_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context009 1333 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 16 SevenLowerFixedCutContexts.context009 1333 9 1155 1332
  · rfl
  · decide
  · exact prefix010_checked
  · exact (SevenLowerFixedCutGroup01.cuts_checked 16)

private theorem prefix008_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context008 1413 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 17 SevenLowerFixedCutContexts.context008 1413 8 1333 1412
  · rfl
  · decide
  · exact prefix009_checked
  · exact (SevenLowerFixedCutGroup01.cuts_checked 17)

private theorem prefix007_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context007 1867 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 18 SevenLowerFixedCutContexts.context007 1867 7 1413 1866
  · rfl
  · decide
  · exact prefix008_checked
  · exact prefix050_checked

private theorem prefix006_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context006 2005 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 19 SevenLowerFixedCutContexts.context006 2005 6 1867 2004
  · rfl
  · decide
  · exact prefix007_checked
  · exact prefix076_checked

private theorem prefix005_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context005 2250 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 20 SevenLowerFixedCutContexts.context005 2250 5 2005 2249
  · rfl
  · decide
  · exact prefix006_checked
  · exact prefix079_checked

private theorem prefix004_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context004 3499 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 21 SevenLowerFixedCutContexts.context004 3499 4 2250 3498
  · rfl
  · decide
  · exact prefix005_checked
  · exact prefix086_checked

private theorem prefix003_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context003 3968 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 22 SevenLowerFixedCutContexts.context003 3968 3 3499 3967
  · rfl
  · decide
  · exact prefix004_checked
  · exact prefix151_checked

private theorem prefix002_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 24 SevenLowerFixedCutContexts.context002 4722 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 23 SevenLowerFixedCutContexts.context002 4722 2 3968 4721
  · rfl
  · decide
  · exact prefix003_checked
  · exact prefix183_checked

private theorem prefix001_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 25 SevenLowerFixedCutContexts.context001 6033 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 24 SevenLowerFixedCutContexts.context001 6033 1 4722 6032
  · rfl
  · decide
  · exact prefix002_checked
  · exact prefix223_checked

private theorem prefix000_checked :
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 26 SevenLowerFixedCutContexts.context000 10813 = true := by
  apply SevenLowerCheckCompose.check_triangle_of_children SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 25 SevenLowerFixedCutContexts.context000 10813 0 6033 10812
  · rfl
  · decide
  · exact prefix001_checked
  · exact prefix262_checked

theorem point_checked : check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles 26 emptyContext 10813 = true := by
  exact prefix000_checked

#print axioms point_checked
end Jsp404.SevenLowerBranchComposedRootCheck
