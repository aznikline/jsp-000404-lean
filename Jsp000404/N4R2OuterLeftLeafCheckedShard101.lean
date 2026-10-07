import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard101
open N4R2OuterLeftReplay

-- Cycle fingerprint 00eff1d6e523a141953b62b39ba71a64adf030d2e659ade290e7f224d093c2d2.
def localCycle00000 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 3 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0439c947a4c805719ce9da783e61133d38eb7588c993487f453e111816598ae5.
def localCycle00001 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 08f33aa34e1fbda2b33b5bf58d466ea508fff96adbff59505ea0672a267aeb50.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 099de4e7cf989d14edcf017670c9e005352a9e76e11d2f2612f196e4e15b8c02.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 5]
    constant := ![0, -1, 3, -1, -1, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 20 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4, .triangle 1 0, .triangle 3 0]

-- Cycle fingerprint 14bd9bb685307c5404c157cc2642b26a5696c681f970257581b2ceefde84f2e1.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 152a2a3a5fbf0364a8597c2879f54eb73aea43949f4571a3914f9edc1fb1162f.
def localCycle00005 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 16529661b1162296b4304e0e2895f54c1a534bde5cdee330b0a2fd43708d1edb.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Cycle fingerprint 19bc701f00fd343c56e73924f8d854414ea82d8abe327f36c0ec5d05f7539d03.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 2554f73aca898eabf26c8a668e00b4bdb8a2e80997ca463fbe2ba15b3161e732.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 276b464868a7e9d91ecff05e3dec4359335aa4a6abc852d7b0dd827b973b6c1e.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .gapLower 2 0]

-- Cycle fingerprint 2e7e0478e6a240fe9136b690e10f4d5c01874ca7163e5a15810c42cdc52ad465.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 306a839c961f204ce8dfe6415a4f4dc9cf963a74752e607fb1d1a93c6041a91a.
def localCycle00011 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 31693938e85e029bfdb5888b26af7e9f6bc675177f0ed722a26cafd5222d7ba5.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 3329ba0dc734532797cca5c76df886a463121350bbcf28075191404d4f9153f5.
def localCycle00013 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 34766f2e0ef9525f0687895e46a8c09845b45b12c382b8e1b60c98252babfab8.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 3518d93c50802ee792ffe097568253a10c4fa834132b3a15a1b15da90fb172d8.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4051d23e4449f141ab756166efb913d01a96d8f234607c4dec26761a6c69e8d9.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 4103abbe9d620a4bba606f1d9f7245229084e06fa9343e1cb2e05534090e5cd4.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4446467c0178493426055f8005743b8a2955524961cb148416af78365f60c8a9.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 477441ae4a96f603ebe86e1691f96f92c42b4d7112711cceae8282863382ae69.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4a4c7148096ac8f1f82f4b9fd9f16866000e3405f4642981d9800bd6149db2ae.
def localCycle00020 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4a9b1329ea876682df64545d45d7dee01a3f1a4c6ae4ef3219e241628736546f.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4cb1bd182e2deece7e757c8ad3cfbf3620a4df34d5e0ec713f3ab7c9c2944043.
def localCycle00022 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 514c4ee969b3f8f7e0a3d0868d2e8aade51fb1f65047a35c2674d374310fee40.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 54200d0a36cde4f434ed4d6e171436a8112dee049fb33a8af1e759b4434d03d4.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 5451f7911536a37581b67d5f77ecc4cc4965d584175a813b9368bbf12ed84181.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 55144c29585cc5cfbacfe6587adff3cb7233f0c8b394df1353450c57ebc12ccd.
def localCycle00026 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 20 1, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 569ab3219c17e76b88281c09aa37d2aae671dad9dad1134ac8255fec1e890040.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 57f1b5264a7c14f5bc674e2e51b27e319db4564b5d943352b57d9ae4fe25a55b.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![0, 2, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 3 2, .gapUpper 5 5, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 1 0]

-- Cycle fingerprint 5a957860fe73888b917ad4a2393a394ee704d3bcb1dbc18263b94348b0a20285.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 5bf312d575be89c3ce2f6e9b1e3bc5a591edd1bd6e3c1a8b7904445ed4c40c99.
def localCycle00030 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5cd0001a1b3f214ba5d4024442f4f332578a68f0c53dcf4a2b0ff0747494bbce.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4]
    constant := ![-1, 0, -1, -1, 0, 0, 3, -1, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 9 0, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 23 0, .triangle 32 0]

-- Cycle fingerprint 5ec14323af914c11ca4b997d302666e59151492c1b37bd2646d9f32db7d10901.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 17 0, .gapLower 2 0]

-- Cycle fingerprint 646d8efcc718798c1bb35e5a554194f57cdddea50ce7320726d51945c4f229d1.
def localCycle00033 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 661c9f74d7e699221d866f1cb12cd5cf9b2de35d97a4132d4d28f8df2559e1fa.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 699312d0d6fb2d910248b4c672eb2b495431e26016d8db64d2bde0a169a28fde.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6b0b54b63bcbe2b445dbbc57047247ba84ff8c7d1bdaf7c85528e7f25952c512.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 6ba191524950544e3b312c2d68c091fa13fe755e40f130d7c220e06cc5f84449.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 6f980903454bfd898f174fe5faf34a164d043a9b2e9a2b48bf1f7090832287d4.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 72d3188865fe266fdf68e34b77b4cc3598a84a57c3bedcb8ee122d8aa3902a79.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7539c125768e5e2ae1e67ccdc92161a768c5f15750ec016544724103e7a86b11.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 77122bd8bdd245d17327393eee27d53ce38083d78d7974f12dbfbddf59c29448.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 2, .triangle 4 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 7747e6a647edf4d624694edbf771ec9ecdd310917800998391a3982cd8b684dd.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 778c31056b8d7529ed5b4c034844e7f71500f00f6b639106b695387848986fea.
def localCycle00043 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 783c7f2534cf08aa2f71c6dd246efc833ca2e1953cca9e80be11234dccc17338.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7ac87942178b32e60acd2c6c9f35f8a84b81b814f9fcb49fc5dd5a7ac3245812.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 7b329e99e755d51319f40a40d9d0822f60fd095afdbc9afc35cbfb861f1d4bb0.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2]

-- Cycle fingerprint 7c062097c4c6d96a220c2b8f35f1192c06bcef62805e5c8fe1c81b8af84bc0e9.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7c681e1a3f0962c4918e356e08e7a7db45a321c9865aa7ac70ebcb0f04410393.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 4 0, .triangle 21 1, .corridorLower 3 6]

-- Cycle fingerprint 7db97e9fec6408a7a61d8c617ed86af4ddbac0648706360e08ccd14b63b5b991.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8169b6949708462fc83b2cc8147eed07dc8065fc8c5eff5d1948ed8469fd6360.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 8328e82977ff19ed791fd346372cc281402110abbb95a4bb1b41b4e787cc9e8c.
def localCycle00051 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 84e3a278fe473a451a048f786862b3eda8951361e07ae219377ecef029baa9f3.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6]
    constant := ![-1, 0, -1, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 4, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0]

-- Cycle fingerprint 852514eb1257b255a3ad0254c3315234e05645632b33b10a6fed1c8a12fbe4bb.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 86ab9c2c49d9579f326ecefbb48e6dd0addb9d2e4ad26f3e127f23ac395e44ca.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 884ddbda68a7e989fa07c1692416ee3263e75fee8be9fb71b9b9c23bec7b5272.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 18 2, .triangle 21 1, .corridorLower 3 6]

-- Cycle fingerprint 90e800af2b5ea28d5e6c32d631a5bf0dbba9215250c3387fb9daa5bb875446e8.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 98f45df20a466271ce13ec1ebac8d7fbd1aa8ce530222d1f26402cedd69bdec3.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 9ff63e3cf19b87ec62537b1e276d85f279d546d4707b6d0963d1125780526dfe.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint a0b2547345a72348e9ed34ac943af73d0e02379c27108f8a716681ba4dcb8c7d.
def localCycle00059 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint a114e10eb331a92b820653a1996f2f2a174684b4cfc3f10d959f62d857ba16e8.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint a1172a829bd89d03bd6a0be7f96cfba1272073ca75be1fd714748e3f4bae9e18.
def localCycle00061 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint a7123ad537bcef942895c957642286f45c404b8bab3509c72537dbb913ecdf6c.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 20 0, .triangle 19 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint ab0a42a03e39e1c5a44df26db9f48b940b0771e5beb9c496b97100bc55396502.
def localCycle00063 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint abca77845c0a264afdcbd512b1fbcc99ca5303abd834f1766947518bfd55e2c7.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint afc107e6e524bd4b0d5defcf18233a81c11d3bc276d5a5d20cfc9c3239f88b2a.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5]
    constant := ![0, -1, 0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4, .triangle 1 0, .triangle 3 0, .triangle 20 1]

-- Cycle fingerprint b05d23e3b1743dd21acc22810bb33eea367edcdcb8e8e25d88f8847900562d17.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint b8df387b524a4df9290921db058818d3cea933a4ed3c9e8aadae89fe6c8ebed7.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 5, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 2, .gapUpper 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint bb151bd557d09c6be5626e35b386eedbc6837327fe297fff814c38fb2c47b1e9.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint be0577dc057750770a16c621af5c51b1c4ed2845a4ada18061856169066c4187.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint bed17062aa2fcde387d065af5f802581375e9a49f58080fb6629f3bf08678af1.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c0fe9b37db6a8777229f3f1447f4df26f675828ebafd7487601a75eaf0e02235.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c423e5183aef636a4ade565eadaa3d2c06f10337398c5db5b71b25dbe817f926.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint c46fd54aaf293fd96ede6205bc9e9a5da49482960a4bf5ffeea5ac16d2e535ba.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint c47cdc3b12b825d1ca435469607ff013ddfac2c956ab82ec6898f82427fc2138.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint cb990b8452ad6c46776c848645105e83c952a9ef251770132f41737347d2cfaa.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint cfecf1b93a1840470b365c0ad0224574cbb0ced33d7d3b7110ccb67b2fb90f0e.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d208e34562a9ebb95675c48c2838f7a38bff8161da6ebd1f73c787de206fa9cb.
def localCycle00077 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d6caa96722967031ffe73f9e35726796c227e31f3f59d704e11b3a9f9e680003.
def localCycle00078 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d6ed9c9630cd4b5a64fd61be58ddfaa07b4066c27828db97c8b22b1c89b14623.
def localCycle00079 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d8db6073f836e5f6dfedb6a8df959142845811923251584c2ac65bc47d6bc54d.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint dbfe3b51eb0761a5396081a1181d2e32c39a053654047adb80f2d26d611f1ded.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint deecd3c83e6b66d8408396476966ace7c3dec4e37777e925d6696558ba94013b.
def localCycle00082 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ebadb180d36614c35ff0cd65fb8561490f3903a04d48b47604fa28e92939d4be.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint ec469daf790bbe154aea7eb186f4e7faec03f7c4afdaf34fcfa0b096da78ebc8.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint ec53a8e83c07017d32e4bed4a9303179b48d9118c600e4f010aeb5b46eac9241.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint fa3dac19bba0298f18f3f66501ff960d493868c79266bf4bf6c47dd2ecb9089c.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint fb69b2c0de5fed49d1b0df78e0de070d79bad4004d5ca5dcb128a89128428f48.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint fb8ceb9a4fd50a218d73069595eb5e614ca7b1ed2224675a440fc5a6e0df9ccb.
def localCycle00088 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint fe25ac2db5135f56aaf7449fcaee0a44f0b4c5a876767d5eee5ab47a6812e537.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint fe493d098a6ca42ec025c6cee27ed4eb7531a97b8b45b1bd409483e7a4b87102.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

def library : Library := fun id => if id < 45 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 39 then (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)))) else (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))))) else (if id < 68 then (if id < 56 then (if id < 50 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))))) else (if id < 62 then (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)))) else (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))))) else (if id < 79 then (if id < 73 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 76 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))))) else (if id < 85 then (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))) else (if id < 88 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 80 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12928)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 44 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12929)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 48 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12930)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 87 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12931)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 44 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12932)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 69 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12933)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 23 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12934)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 17 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12935)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 1, 0, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 74 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12936)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 1, 0, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 65 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12937)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 6, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 1, 0, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 39 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12938)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 1, 0, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 68 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12939)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 3, 6, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 39 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12940)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 66 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12941)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 5, 1, 6, 3, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 10 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12942)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 43 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12943)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 1, 0, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 65 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12944)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 6, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 1, 0, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 78 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12945)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 1, 0, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 68 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12946)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 3, 6, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 78 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12947)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 66 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12948)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 5, 1, 6, 3, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 10 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12949)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 5, 6, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 0, 5, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 70 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12950)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 5, 6, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 70 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12951)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 75 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12952)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 54 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12953)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 18 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12954)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 73 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12955)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 6, 0, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 2, 0]], proof := .tail 15 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12956)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 0, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 54 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12957)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 18 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12958)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 55 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12959)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 0, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 25 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12960)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 33 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12961)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 22 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12962)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 5, 0, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12963)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 5, 0, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 42 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12964)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 5, 0, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 16 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12965)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 5, 0, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 1, 2, 0, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 3 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12966)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 3, 6, 4], ![1, 5, 0, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 1, 2, 0, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 21 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12967)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 6, 3, 4], ![1, 5, 0, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 1, 2, 0, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 9 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12968)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 2, 1, 3, 6, 4], ![2, 5, 0, 3, 6, 4], ![1, 5, 0, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 85 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12969)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 2, 1, 3, 6, 4], ![2, 5, 0, 6, 3, 4], ![1, 5, 0, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 32 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12970)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 2, 1, 6, 3, 4], ![2, 5, 0, 6, 3, 4], ![1, 5, 0, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 24 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12971)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 2, 6, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 5, 0, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 86 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12972)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 6, 2, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 5, 6, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 86 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12973)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 5, 6, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 75 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12974)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 6, 5, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 56 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12975)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 5, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 54 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12976)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 5, 0, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 18 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12977)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 5, 0, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 67 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12978)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 5, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 60 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12979)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 5, 0, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 6 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12980)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 5, 0, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 90 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12981)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 3, 4, 6], ![5, 1, 0, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12982)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 3, 4, 6], ![5, 1, 0, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 2 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12983)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 3, 4, 6], ![5, 1, 0, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 64 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12984)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 3, 4, 6], ![5, 1, 0, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 2, 1, 0, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 57 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12985)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 3, 6, 4], ![5, 1, 0, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 45 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12986)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 6, 3, 4], ![5, 1, 0, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 34 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12987)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 2, 1, 3, 6, 4], ![5, 2, 0, 3, 6, 4], ![5, 1, 0, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 45 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12988)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 2, 1, 3, 6, 4], ![5, 2, 0, 6, 3, 4], ![5, 1, 0, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 34 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12989)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 2, 1, 6, 3, 4], ![5, 2, 0, 6, 3, 4], ![5, 1, 0, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 41 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12990)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 2, 6, 1, 3, 4], ![5, 2, 6, 0, 3, 4], ![5, 1, 0, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 89 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12991)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 6, 2, 1, 3, 4], ![5, 2, 6, 0, 3, 4], ![5, 1, 6, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 58 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12992)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![5, 2, 6, 0, 3, 4], ![5, 1, 6, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 75 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12993)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 6, 2, 1, 3, 4], ![5, 6, 2, 0, 3, 4], ![5, 6, 1, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 50 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12994)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![5, 6, 2, 0, 3, 4], ![5, 6, 1, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 75 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12995)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 3, 4], ![5, 6, 1, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 54 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12996)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 3, 4], ![6, 5, 1, 0, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 29 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12997)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 3, 4], ![6, 5, 1, 0, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12998)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 3, 4], ![6, 5, 1, 0, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 37 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12999)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 1, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 47 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13000)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 1, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 82 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13001)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 26 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13002)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 88 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13003)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 11 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13004)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 6, 4, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 30 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13005)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 38 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13006)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 19 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13007)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 81 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13008)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 79 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13009)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 76 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13010)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 36 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13011)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 77 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13012)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 38 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13013)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 19 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13014)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 81 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13015)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 79 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13016)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 76 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13017)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 36 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13018)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 20 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13019)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 3, 1, 2]], proof := .tail 12 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13020)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 7 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13021)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 7 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13022)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 7 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13023)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 4, 3, 5], ![6, 1, 0, 4, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13024)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 1, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 51 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13025)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 1, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 61 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13026)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 40 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13027)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 62 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13028)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 6, 5, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 8 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13029)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 52 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13030)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 6, 4, 5, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 71 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13031)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 6, 4, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 13 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13032)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 49 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13033)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 4, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 81 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13034)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 63 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13035)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 76 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13036)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 31 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13037)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 0 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13038)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 49 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13039)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 4, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 81 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13040)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 63 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13041)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 76 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13042)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 31 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13043)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 35 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13044)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 0, 3, 1, 2]], proof := .tail 72 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13045)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 4 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13046)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 4, 3, 5], ![1, 0, 6, 4, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 4 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13047)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 4 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13048)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 4, 3, 5], ![6, 1, 0, 4, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 14 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13049)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 5, 4, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 1, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13050)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 5, 4, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 83 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13051)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 5, 6, 4, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 1 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13052)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 6, 5, 4, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 84 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13053)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 6, 5, 4, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 1, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 53 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13054)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 6, 5, 4, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 46 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13055)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (12928 + j.val))) (lookup j.val) = true := by
  have hjbound : j.val < 128 := j.isLt
  by_cases h64 : j.val < 64
  · by_cases h32 : j.val < 32
    · by_cases h16 : j.val < 16
      · by_cases h8 : j.val < 8
        · by_cases h4 : j.val < 4
          · by_cases h2 : j.val < 2
            · by_cases h1 : j.val < 1
              · have hj : j = ⟨0, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 0
                  omega
                subst j
                exact namedLeaf000_checked
              · have hj : j = ⟨1, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 1
                  omega
                subst j
                exact namedLeaf001_checked
            · by_cases h3 : j.val < 3
              · have hj : j = ⟨2, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 2
                  omega
                subst j
                exact namedLeaf002_checked
              · have hj : j = ⟨3, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 3
                  omega
                subst j
                exact namedLeaf003_checked
          · by_cases h6 : j.val < 6
            · by_cases h5 : j.val < 5
              · have hj : j = ⟨4, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 4
                  omega
                subst j
                exact namedLeaf004_checked
              · have hj : j = ⟨5, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 5
                  omega
                subst j
                exact namedLeaf005_checked
            · by_cases h7 : j.val < 7
              · have hj : j = ⟨6, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 6
                  omega
                subst j
                exact namedLeaf006_checked
              · have hj : j = ⟨7, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 7
                  omega
                subst j
                exact namedLeaf007_checked
        · by_cases h12 : j.val < 12
          · by_cases h10 : j.val < 10
            · by_cases h9 : j.val < 9
              · have hj : j = ⟨8, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 8
                  omega
                subst j
                exact namedLeaf008_checked
              · have hj : j = ⟨9, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 9
                  omega
                subst j
                exact namedLeaf009_checked
            · by_cases h11 : j.val < 11
              · have hj : j = ⟨10, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 10
                  omega
                subst j
                exact namedLeaf010_checked
              · have hj : j = ⟨11, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 11
                  omega
                subst j
                exact namedLeaf011_checked
          · by_cases h14 : j.val < 14
            · by_cases h13 : j.val < 13
              · have hj : j = ⟨12, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 12
                  omega
                subst j
                exact namedLeaf012_checked
              · have hj : j = ⟨13, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 13
                  omega
                subst j
                exact namedLeaf013_checked
            · by_cases h15 : j.val < 15
              · have hj : j = ⟨14, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 14
                  omega
                subst j
                exact namedLeaf014_checked
              · have hj : j = ⟨15, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 15
                  omega
                subst j
                exact namedLeaf015_checked
      · by_cases h24 : j.val < 24
        · by_cases h20 : j.val < 20
          · by_cases h18 : j.val < 18
            · by_cases h17 : j.val < 17
              · have hj : j = ⟨16, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 16
                  omega
                subst j
                exact namedLeaf016_checked
              · have hj : j = ⟨17, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 17
                  omega
                subst j
                exact namedLeaf017_checked
            · by_cases h19 : j.val < 19
              · have hj : j = ⟨18, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 18
                  omega
                subst j
                exact namedLeaf018_checked
              · have hj : j = ⟨19, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 19
                  omega
                subst j
                exact namedLeaf019_checked
          · by_cases h22 : j.val < 22
            · by_cases h21 : j.val < 21
              · have hj : j = ⟨20, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 20
                  omega
                subst j
                exact namedLeaf020_checked
              · have hj : j = ⟨21, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 21
                  omega
                subst j
                exact namedLeaf021_checked
            · by_cases h23 : j.val < 23
              · have hj : j = ⟨22, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 22
                  omega
                subst j
                exact namedLeaf022_checked
              · have hj : j = ⟨23, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 23
                  omega
                subst j
                exact namedLeaf023_checked
        · by_cases h28 : j.val < 28
          · by_cases h26 : j.val < 26
            · by_cases h25 : j.val < 25
              · have hj : j = ⟨24, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 24
                  omega
                subst j
                exact namedLeaf024_checked
              · have hj : j = ⟨25, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 25
                  omega
                subst j
                exact namedLeaf025_checked
            · by_cases h27 : j.val < 27
              · have hj : j = ⟨26, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 26
                  omega
                subst j
                exact namedLeaf026_checked
              · have hj : j = ⟨27, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 27
                  omega
                subst j
                exact namedLeaf027_checked
          · by_cases h30 : j.val < 30
            · by_cases h29 : j.val < 29
              · have hj : j = ⟨28, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 28
                  omega
                subst j
                exact namedLeaf028_checked
              · have hj : j = ⟨29, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 29
                  omega
                subst j
                exact namedLeaf029_checked
            · by_cases h31 : j.val < 31
              · have hj : j = ⟨30, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 30
                  omega
                subst j
                exact namedLeaf030_checked
              · have hj : j = ⟨31, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 31
                  omega
                subst j
                exact namedLeaf031_checked
    · by_cases h48 : j.val < 48
      · by_cases h40 : j.val < 40
        · by_cases h36 : j.val < 36
          · by_cases h34 : j.val < 34
            · by_cases h33 : j.val < 33
              · have hj : j = ⟨32, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 32
                  omega
                subst j
                exact namedLeaf032_checked
              · have hj : j = ⟨33, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 33
                  omega
                subst j
                exact namedLeaf033_checked
            · by_cases h35 : j.val < 35
              · have hj : j = ⟨34, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 34
                  omega
                subst j
                exact namedLeaf034_checked
              · have hj : j = ⟨35, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 35
                  omega
                subst j
                exact namedLeaf035_checked
          · by_cases h38 : j.val < 38
            · by_cases h37 : j.val < 37
              · have hj : j = ⟨36, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 36
                  omega
                subst j
                exact namedLeaf036_checked
              · have hj : j = ⟨37, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 37
                  omega
                subst j
                exact namedLeaf037_checked
            · by_cases h39 : j.val < 39
              · have hj : j = ⟨38, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 38
                  omega
                subst j
                exact namedLeaf038_checked
              · have hj : j = ⟨39, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 39
                  omega
                subst j
                exact namedLeaf039_checked
        · by_cases h44 : j.val < 44
          · by_cases h42 : j.val < 42
            · by_cases h41 : j.val < 41
              · have hj : j = ⟨40, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 40
                  omega
                subst j
                exact namedLeaf040_checked
              · have hj : j = ⟨41, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 41
                  omega
                subst j
                exact namedLeaf041_checked
            · by_cases h43 : j.val < 43
              · have hj : j = ⟨42, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 42
                  omega
                subst j
                exact namedLeaf042_checked
              · have hj : j = ⟨43, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 43
                  omega
                subst j
                exact namedLeaf043_checked
          · by_cases h46 : j.val < 46
            · by_cases h45 : j.val < 45
              · have hj : j = ⟨44, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 44
                  omega
                subst j
                exact namedLeaf044_checked
              · have hj : j = ⟨45, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 45
                  omega
                subst j
                exact namedLeaf045_checked
            · by_cases h47 : j.val < 47
              · have hj : j = ⟨46, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 46
                  omega
                subst j
                exact namedLeaf046_checked
              · have hj : j = ⟨47, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 47
                  omega
                subst j
                exact namedLeaf047_checked
      · by_cases h56 : j.val < 56
        · by_cases h52 : j.val < 52
          · by_cases h50 : j.val < 50
            · by_cases h49 : j.val < 49
              · have hj : j = ⟨48, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 48
                  omega
                subst j
                exact namedLeaf048_checked
              · have hj : j = ⟨49, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 49
                  omega
                subst j
                exact namedLeaf049_checked
            · by_cases h51 : j.val < 51
              · have hj : j = ⟨50, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 50
                  omega
                subst j
                exact namedLeaf050_checked
              · have hj : j = ⟨51, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 51
                  omega
                subst j
                exact namedLeaf051_checked
          · by_cases h54 : j.val < 54
            · by_cases h53 : j.val < 53
              · have hj : j = ⟨52, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 52
                  omega
                subst j
                exact namedLeaf052_checked
              · have hj : j = ⟨53, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 53
                  omega
                subst j
                exact namedLeaf053_checked
            · by_cases h55 : j.val < 55
              · have hj : j = ⟨54, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 54
                  omega
                subst j
                exact namedLeaf054_checked
              · have hj : j = ⟨55, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 55
                  omega
                subst j
                exact namedLeaf055_checked
        · by_cases h60 : j.val < 60
          · by_cases h58 : j.val < 58
            · by_cases h57 : j.val < 57
              · have hj : j = ⟨56, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 56
                  omega
                subst j
                exact namedLeaf056_checked
              · have hj : j = ⟨57, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 57
                  omega
                subst j
                exact namedLeaf057_checked
            · by_cases h59 : j.val < 59
              · have hj : j = ⟨58, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 58
                  omega
                subst j
                exact namedLeaf058_checked
              · have hj : j = ⟨59, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 59
                  omega
                subst j
                exact namedLeaf059_checked
          · by_cases h62 : j.val < 62
            · by_cases h61 : j.val < 61
              · have hj : j = ⟨60, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 60
                  omega
                subst j
                exact namedLeaf060_checked
              · have hj : j = ⟨61, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 61
                  omega
                subst j
                exact namedLeaf061_checked
            · by_cases h63 : j.val < 63
              · have hj : j = ⟨62, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 62
                  omega
                subst j
                exact namedLeaf062_checked
              · have hj : j = ⟨63, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 63
                  omega
                subst j
                exact namedLeaf063_checked
  · by_cases h96 : j.val < 96
    · by_cases h80 : j.val < 80
      · by_cases h72 : j.val < 72
        · by_cases h68 : j.val < 68
          · by_cases h66 : j.val < 66
            · by_cases h65 : j.val < 65
              · have hj : j = ⟨64, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 64
                  omega
                subst j
                exact namedLeaf064_checked
              · have hj : j = ⟨65, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 65
                  omega
                subst j
                exact namedLeaf065_checked
            · by_cases h67 : j.val < 67
              · have hj : j = ⟨66, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 66
                  omega
                subst j
                exact namedLeaf066_checked
              · have hj : j = ⟨67, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 67
                  omega
                subst j
                exact namedLeaf067_checked
          · by_cases h70 : j.val < 70
            · by_cases h69 : j.val < 69
              · have hj : j = ⟨68, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 68
                  omega
                subst j
                exact namedLeaf068_checked
              · have hj : j = ⟨69, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 69
                  omega
                subst j
                exact namedLeaf069_checked
            · by_cases h71 : j.val < 71
              · have hj : j = ⟨70, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 70
                  omega
                subst j
                exact namedLeaf070_checked
              · have hj : j = ⟨71, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 71
                  omega
                subst j
                exact namedLeaf071_checked
        · by_cases h76 : j.val < 76
          · by_cases h74 : j.val < 74
            · by_cases h73 : j.val < 73
              · have hj : j = ⟨72, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 72
                  omega
                subst j
                exact namedLeaf072_checked
              · have hj : j = ⟨73, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 73
                  omega
                subst j
                exact namedLeaf073_checked
            · by_cases h75 : j.val < 75
              · have hj : j = ⟨74, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 74
                  omega
                subst j
                exact namedLeaf074_checked
              · have hj : j = ⟨75, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 75
                  omega
                subst j
                exact namedLeaf075_checked
          · by_cases h78 : j.val < 78
            · by_cases h77 : j.val < 77
              · have hj : j = ⟨76, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 76
                  omega
                subst j
                exact namedLeaf076_checked
              · have hj : j = ⟨77, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 77
                  omega
                subst j
                exact namedLeaf077_checked
            · by_cases h79 : j.val < 79
              · have hj : j = ⟨78, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 78
                  omega
                subst j
                exact namedLeaf078_checked
              · have hj : j = ⟨79, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 79
                  omega
                subst j
                exact namedLeaf079_checked
      · by_cases h88 : j.val < 88
        · by_cases h84 : j.val < 84
          · by_cases h82 : j.val < 82
            · by_cases h81 : j.val < 81
              · have hj : j = ⟨80, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 80
                  omega
                subst j
                exact namedLeaf080_checked
              · have hj : j = ⟨81, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 81
                  omega
                subst j
                exact namedLeaf081_checked
            · by_cases h83 : j.val < 83
              · have hj : j = ⟨82, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 82
                  omega
                subst j
                exact namedLeaf082_checked
              · have hj : j = ⟨83, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 83
                  omega
                subst j
                exact namedLeaf083_checked
          · by_cases h86 : j.val < 86
            · by_cases h85 : j.val < 85
              · have hj : j = ⟨84, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 84
                  omega
                subst j
                exact namedLeaf084_checked
              · have hj : j = ⟨85, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 85
                  omega
                subst j
                exact namedLeaf085_checked
            · by_cases h87 : j.val < 87
              · have hj : j = ⟨86, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 86
                  omega
                subst j
                exact namedLeaf086_checked
              · have hj : j = ⟨87, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 87
                  omega
                subst j
                exact namedLeaf087_checked
        · by_cases h92 : j.val < 92
          · by_cases h90 : j.val < 90
            · by_cases h89 : j.val < 89
              · have hj : j = ⟨88, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 88
                  omega
                subst j
                exact namedLeaf088_checked
              · have hj : j = ⟨89, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 89
                  omega
                subst j
                exact namedLeaf089_checked
            · by_cases h91 : j.val < 91
              · have hj : j = ⟨90, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 90
                  omega
                subst j
                exact namedLeaf090_checked
              · have hj : j = ⟨91, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 91
                  omega
                subst j
                exact namedLeaf091_checked
          · by_cases h94 : j.val < 94
            · by_cases h93 : j.val < 93
              · have hj : j = ⟨92, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 92
                  omega
                subst j
                exact namedLeaf092_checked
              · have hj : j = ⟨93, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 93
                  omega
                subst j
                exact namedLeaf093_checked
            · by_cases h95 : j.val < 95
              · have hj : j = ⟨94, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 94
                  omega
                subst j
                exact namedLeaf094_checked
              · have hj : j = ⟨95, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 95
                  omega
                subst j
                exact namedLeaf095_checked
    · by_cases h112 : j.val < 112
      · by_cases h104 : j.val < 104
        · by_cases h100 : j.val < 100
          · by_cases h98 : j.val < 98
            · by_cases h97 : j.val < 97
              · have hj : j = ⟨96, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 96
                  omega
                subst j
                exact namedLeaf096_checked
              · have hj : j = ⟨97, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 97
                  omega
                subst j
                exact namedLeaf097_checked
            · by_cases h99 : j.val < 99
              · have hj : j = ⟨98, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 98
                  omega
                subst j
                exact namedLeaf098_checked
              · have hj : j = ⟨99, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 99
                  omega
                subst j
                exact namedLeaf099_checked
          · by_cases h102 : j.val < 102
            · by_cases h101 : j.val < 101
              · have hj : j = ⟨100, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 100
                  omega
                subst j
                exact namedLeaf100_checked
              · have hj : j = ⟨101, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 101
                  omega
                subst j
                exact namedLeaf101_checked
            · by_cases h103 : j.val < 103
              · have hj : j = ⟨102, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 102
                  omega
                subst j
                exact namedLeaf102_checked
              · have hj : j = ⟨103, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 103
                  omega
                subst j
                exact namedLeaf103_checked
        · by_cases h108 : j.val < 108
          · by_cases h106 : j.val < 106
            · by_cases h105 : j.val < 105
              · have hj : j = ⟨104, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 104
                  omega
                subst j
                exact namedLeaf104_checked
              · have hj : j = ⟨105, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 105
                  omega
                subst j
                exact namedLeaf105_checked
            · by_cases h107 : j.val < 107
              · have hj : j = ⟨106, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 106
                  omega
                subst j
                exact namedLeaf106_checked
              · have hj : j = ⟨107, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 107
                  omega
                subst j
                exact namedLeaf107_checked
          · by_cases h110 : j.val < 110
            · by_cases h109 : j.val < 109
              · have hj : j = ⟨108, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 108
                  omega
                subst j
                exact namedLeaf108_checked
              · have hj : j = ⟨109, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 109
                  omega
                subst j
                exact namedLeaf109_checked
            · by_cases h111 : j.val < 111
              · have hj : j = ⟨110, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 110
                  omega
                subst j
                exact namedLeaf110_checked
              · have hj : j = ⟨111, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 111
                  omega
                subst j
                exact namedLeaf111_checked
      · by_cases h120 : j.val < 120
        · by_cases h116 : j.val < 116
          · by_cases h114 : j.val < 114
            · by_cases h113 : j.val < 113
              · have hj : j = ⟨112, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 112
                  omega
                subst j
                exact namedLeaf112_checked
              · have hj : j = ⟨113, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 113
                  omega
                subst j
                exact namedLeaf113_checked
            · by_cases h115 : j.val < 115
              · have hj : j = ⟨114, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 114
                  omega
                subst j
                exact namedLeaf114_checked
              · have hj : j = ⟨115, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 115
                  omega
                subst j
                exact namedLeaf115_checked
          · by_cases h118 : j.val < 118
            · by_cases h117 : j.val < 117
              · have hj : j = ⟨116, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 116
                  omega
                subst j
                exact namedLeaf116_checked
              · have hj : j = ⟨117, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 117
                  omega
                subst j
                exact namedLeaf117_checked
            · by_cases h119 : j.val < 119
              · have hj : j = ⟨118, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 118
                  omega
                subst j
                exact namedLeaf118_checked
              · have hj : j = ⟨119, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 119
                  omega
                subst j
                exact namedLeaf119_checked
        · by_cases h124 : j.val < 124
          · by_cases h122 : j.val < 122
            · by_cases h121 : j.val < 121
              · have hj : j = ⟨120, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 120
                  omega
                subst j
                exact namedLeaf120_checked
              · have hj : j = ⟨121, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 121
                  omega
                subst j
                exact namedLeaf121_checked
            · by_cases h123 : j.val < 123
              · have hj : j = ⟨122, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 122
                  omega
                subst j
                exact namedLeaf122_checked
              · have hj : j = ⟨123, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 123
                  omega
                subst j
                exact namedLeaf123_checked
          · by_cases h126 : j.val < 126
            · by_cases h125 : j.val < 125
              · have hj : j = ⟨124, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 124
                  omega
                subst j
                exact namedLeaf124_checked
              · have hj : j = ⟨125, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 125
                  omega
                subst j
                exact namedLeaf125_checked
            · by_cases h127 : j.val < 127
              · have hj : j = ⟨126, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 126
                  omega
                subst j
                exact namedLeaf126_checked
              · have hj : j = ⟨127, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 127
                  omega
                subst j
                exact namedLeaf127_checked

theorem correct (id : Fin 24698) (hlow : 12928 ≤ id.val) (hhigh : id.val < 13056) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 12928)) = true := by
  let j : Fin 128 := ⟨id.val - 12928, by omega⟩
  have hsum : 12928 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (12928 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard101
