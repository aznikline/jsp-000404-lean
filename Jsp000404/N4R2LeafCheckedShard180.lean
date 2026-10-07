import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard180
open N4R2RowDataReplay

-- Original cycle 0036d6f26e63ff09f3c81fcdf1279cd6c042f30acd5b0b8ed118f8a88a71067f; original global index 20.
def localCycle00000 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 01277ec6e886e0ea1d0835a8d7130246d9613c34884a02f658e877c7f453bb2b; original global index 102.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Original cycle 06bee4984fa021fbc6470f4c57e5008443cb342aebb0943e47de5d14debeccb7; original global index 553.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 0c3ddc95deb38715e262d56c5e8ae101ccd6cf3eaa4216f81fcace21a5c2404b; original global index 966.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 0e3a6935d0142548bd031244440f509bb47a3a68ddc1798132fea111cbc3cd53; original global index 1121.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 127eb4cc0a031362cc29e395386bd52e508655ff0c8c2908a452a6bb66c8514a; original global index 1465.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 13ab9223e384bcae4adda25e529fddb27557ddd67c589463edd19c01586a5765; original global index 1554.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 15a81751053e30002942a649e0de165b835a8070a645726f3c687f938e543434; original global index 1718.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 1adf0d73a09ea3cf3ba7e2589ec1f54d003e2280b9b5aac2a3320b00e40b597f; original global index 2084.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 1, .corridorUpper 0 1, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaLower 4]

-- Original cycle 1e2028aacab03d06787d4b89648c37ddbdc5cb2ee6277086c2aa1af472f37f51; original global index 2316.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .gapLower 2 3, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 1f497db3cfff2c043db41af71e0aff617b64aa62b50b8052578ab4fd20705728; original global index 2400.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 1f7d53cc92e1d19a6bed8002947e4255d35ebb8a1e5e655bb0a0476e02929473; original global index 2418.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 22f8e5754b2ba466704010095c2ad5b5d6da69024c99e4e471b10381abd8353e; original global index 2682.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 270ca04fd4b27325b408129fcc65172d1492d8a02b79bf528a52fcb3521c9f84; original global index 2993.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 27499bfc29eb446224c3597c7b1f1fcde72986b2fbbc6e627f13ca6680297f57; original global index 3007.
def localCycle00014 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 29dd9f23dd95bbd780ce82a31bf658ac78f3dbea665a65140cc96af7b982796a; original global index 3195.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 2d009fdd60bfdfe75cb278fe60304d851e154bf77ff6099fae2292e7180b4ddf; original global index 3438.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 31850bfca61ab849e5f41a9b2dac0aba5906187442bbae182e6700153559c0da; original global index 3776.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .corridorLower 2 4]

-- Original cycle 33b729c35a870af38731c270ba2ee67db0c37e92efaec2fa1c30460ec1737ee2; original global index 3959.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3acad0eaef8d097eea78d11a5efe194ad2eb3ea14e79184b5780bdf91a8fc0fc; original global index 4542.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 3b19e880c4026558da5ba20bd8e4f6d32173fe3653a47d400b2cc4f5922aa355; original global index 4569.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3eb67ba34dcfbff8cb58c54a6dfd39b6dff9e793e95220eddb5f447ea7f7d54f; original global index 4849.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 3edb46275e0a1d298c7ebe3c684639f276dbfdb9dca1c7d298978cb6e3d6ff82; original global index 4858.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 5]

-- Original cycle 3f350a81d8fd881d668f51852c8ae0d784e95618277f4990461d5e6d05ad29b5; original global index 4879.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle 413bc8d683b8e16306683fed8bcba515ef2bf8e55abb3724b9896c864ef0446b; original global index 5033.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 4304944402c763cec294c0b7ffc65472cf8325897773a335fca5a6997e9450cd; original global index 5170.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4967b209ab89732a4122db95a6362eb2c4ee4158fb3c560177ee4001774f158e; original global index 5687.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4a97387d5d73782fffd2fbe982dc3598c456957ca428f432b57e4ba457df65b1; original global index 5787.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 4aba6fdce6bd06e9199bc8d0be77e57acc945b61621013916fdfb247e77651d6; original global index 5798.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 4ac9e35ff2a0ffeaa1ce19ecb2480ea160ab12a832a38f02e8d1d3b7595881fe; original global index 5804.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 4bcdd41a0947c55582c2e4637aecb7974045bfcabee76748d2518d9ca3bd6726; original global index 5886.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .corridorLower 2 4]

-- Original cycle 4f9fd991ebd572026ff753401d7712a4fb4117712f411a79a0709deba6ed769e; original global index 6182.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 51b2433900584d289fbe76b056f359f61033d02e7ebc23dfb25a1700c5abfac5; original global index 6360.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 56295f3197788c0931a5fae15cfd21c5a6d9620069148e4e13d8e7440ff9e7bb; original global index 6682.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 15 1, .triangle 16 0, .corridorLower 2 4]

-- Original cycle 57ef1ac5dacd2ab6059310bb60769e9496ef0c0825e5e29d130170303cff73e3; original global index 6823.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5abe9e24f0b705d377e8ae62960643b16de229e988867afa4ff8b70b3805a6a3; original global index 7066.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5c03ab62046fd76431421815d9c30f26f6f1b0e2d1d20bf062795afaaed55b4f; original global index 7160.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5d10d11a855c6180da0eb2ef72f5e91586987acd232575106cfdf7f06b9e9e3c; original global index 7243.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 5ef524325791f9ac5e1d351d6f234510d99edc9b37583c2398ea1494d78c85e9; original global index 7393.
def localCycle00038 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 2, .gapUpper 1 5]

-- Original cycle 613051c569e4fe2b479b3cdb7bce3205a1966e95603d1bd1c46abe680e0c9d92; original global index 7580.
def localCycle00039 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 61de00de297dd5432b53f7badc60d80fcb68ccdd9f2d4e1f50a6300371a1d801; original global index 7640.
def localCycle00040 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 2, .gapUpper 2 4]

-- Original cycle 6b16cbd120934c36b9650510f99bd60f06025b4c369289ee6cd4add9628a2d1f; original global index 8336.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 6bf073fb1d9c14d712d64d22865dc2f817029a3f6f9749b557669f3544173716; original global index 8413.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .triangle 21 2, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4]

-- Original cycle 6ec4b2e766865cf4cc54342b93c08903ab4fc108d40a5d323034b472b529e38c; original global index 8595.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 76329fe036ab3a5edc496bf02fb7ae549502a1020a5b976a2f752cbc8549dd98; original global index 9151.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 77734c34205add6d66dd8293cd9085b83b5248a1987f8fc33d7572abede4a4f3; original global index 9241.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 77a1014c37395ecaa73c91e120a33db66dfedef36e76a8b59248e6526a056bc8; original global index 9255.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7fb37ddd4b810e0e8bdb2fa6b25b06aa3bfa6f848bf8ec348cbef19fdf318426; original global index 9902.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Original cycle 8232c127d720529e73141b297b3b61d38e1ad0b1b7bb7c474801e56d1570e957; original global index 10113.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 85e6557cb36d0c8dcd0f2d399fb77c3ccee42cc5367682e05cb3768eca2c76eb; original global index 10388.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 28 1, .corridorLower 2 4]

-- Original cycle 8a4db83a3b61e5bb0906b917574e43580a59ec9c167643e38507990171f82d14; original global index 10716.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8acc673a8973760cdf2081932a98541f9100873d05569f27c93bd416f3242fdb; original global index 10755.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 8b6761777b39aaeb64c717f1403e7efe25ae0adb6ac2e7cc8bccbb94d4874ef4; original global index 10802.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 90310aef1310a2d715d8be9ff5e32c547a75efe16d9416230f07c855ea1bf8e0; original global index 11160.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 92fda3b2a1f25d1da3bbeafd93b68611c3e2c1538d702f3703d77778ca153b5f; original global index 11399.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 98ea9ce4b11608d83044a97d4c2328d13e5326ad4c276db3c5b03224d2cc3624; original global index 11873.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 98ec83f677eab082b9d47f2447c1f87aabb6eac35944a9df44c7fefbf56b0218; original global index 11875.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 9a432e57cce88c6cc61ddfa0b2771913f8c40c0ed2f14fac2f616923ce24a810; original global index 11987.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9a9982e9142ddb9b28b6d04a69cbae753d6d704e22fd008ed367e5f9ff3d6e09; original global index 12010.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 9efa841ce9e2e1893016219ffd823cb5e5bc0148550714cde2ad57d1ba6163a7; original global index 12380.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle a4c559ed5f70a59986e0d45c777effd05cf637b919fec7f982671d78f7a67ab3; original global index 12805.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle a7c513f097a46c74606b93bc35bcd3760f385013b0481653f78e589b446b34e6; original global index 13053.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a8c6b50bd152ec30d31fbb84e82dd342ee96fed84efc58adad0c581953a5b2f9; original global index 13135.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle aa131b2656b56c1a3c3764cf24a2cbb5c6e3c26c58f12933dea525ef4f806ece; original global index 13242.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 2, .triangle 18 0, .corridorLower 2 6]

-- Original cycle ac775e871de5a8af5b0a396d2212983ab8191d08d6b560cf504f5bdef81bda32; original global index 13444.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ad3f9b7b9ac6467e15baaa5c92b7256ce77b24845cc11f639cd3004e9986752e; original global index 13506.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle afa34a4a86d5657c42be10781e52c4f2ee2b392290f9e2590e11b68a0bc34a14; original global index 13720.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle b60799ee8ab087da61b5fb0cd5c3b4d9ceff3da4c8565b0bd177a83bb33c354b; original global index 14219.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle ba5e353ce6b622de33f5b8d07882563f25788ef9eb163dae75f4a0c6c897f1f9; original global index 14552.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle bd0976ad1e5223406d06afab717d9b1d923507d979e3e9179468c5edc2c7180f; original global index 14745.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c22bbf2f4b3d08afb9c312dcffadb42f632f80792683aa9abe4db4806dcc7e82; original global index 15161.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c7a88af52aa8227552d0de39852930b90474db5f8ef5e86ef6623fced67af8f7; original global index 15582.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle c88166f2b33490bc4f76b087f3617c6101ba2d17a92f21243b8174885c24620d; original global index 15659.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c905a7aaa173f9dd250f405f02ba91b9a9d85c9d23331a51fd85f0abbdb8af60; original global index 15700.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle cb40660610011407b306483b1e9cae68fe6f50cf806ebc34042a0da4d2c5553c; original global index 15875.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle d0e2caefe8776597ac8af7eab60e75eae44a69985e0ce54b8cc0e719dd745825; original global index 16308.
def localCycle00075 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 2, .gapUpper 1 5]

-- Original cycle d57616ca0d399916fb85080f1e8b7013022f90fcf0f4cd618cabd35c58615eb3; original global index 16664.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d87fa8798f1f731f231e4c230d40794d97f24b536e75ce6e956929ec714cb3b9; original global index 16898.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle da9dc61433ba83fca9a03bee189284183cc32f8e82c19fde230c9ef1e9092d61; original global index 17085.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle dbf04538df2fc61a417f2f0e5f4b57e8c3713b6fe2491b420f4ead4741ff2812; original global index 17191.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle df118089a54cd000c57c42a3097d620e704edc5114866ac8a300205681fe5f4d; original global index 17437.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Original cycle e2261a2864e2c16824b4dcada7950ecf5f9b58f170784ffe562ed9f16ce7f512; original global index 17682.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle e521e656616071977339dfdf53b5bc12ad0fb3ea653e3fc7e7860c658c414f68; original global index 17912.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle e6b774f1dab42ed1ebc93172123e4ef4eeb2db3bfcf20674926ed7796a4d8ac6; original global index 18046.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle e9716c8338318400ae46873528a7692df8e4460a4b71de5c222179329cfe8788; original global index 18242.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Original cycle eb2a4e81ee7ad8fc6499570599bf161447e36b5380e8d610b0f9a596790b2362; original global index 18361.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2]

-- Original cycle ecbd03a5e61c08293ed893a6fb57b708cb24ec2fd9e6563fa51d6a9a8130aaea; original global index 18480.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Original cycle ee3d9bae617e99ddd24d708b4243111fcde6920b48fd391c00fb8b6e44de0772; original global index 18593.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ef17504c06e5e80228c3f48079df607bbe7d2fd8bd1fc4195e8cb0fc7280e60f; original global index 18656.
def localCycle00088 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle f1a0094837c0f1550369cb92ef485e11888a81b9ac04823ba4725a91590798ee; original global index 18840.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f1e748acd1345921b186321708120bd3ac116aa8a0cbb8828aafc950ca3498c6; original global index 18864.
def localCycle00090 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f52ac17666c7b46a7d1bb771ad6027e8ea8308833f6b1cea6267d705fa83bbf9; original global index 19110.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4]

-- Original cycle f5e3226f943a4ad19cd72fd2868b097e7e57d6d5a535e977870faf96a2487336; original global index 19186.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle f629588f106fa830c95737cb344ced501d788b4ffdea8bc4daf98f579e19ffe1; original global index 19205.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4]

-- Original cycle f6e01659b11f90e06b263b8dc97de2a3e13d4fce59b316e1d1b8e6a8fea479cc; original global index 19256.
def localCycle00094 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle f81d6d0702fb71ed6e99d0082c3484ccca4e686cd609037c8992a3bd12636304; original global index 19345.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle fcd9dca0c9bb5dfc7317b65a8aa83f048c2244b57d7f17cfe9c8241fe4ef8d1f; original global index 19760.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Original cycle fcdedc2cb0237ed8f6e44e2f28b1059c889ec38e23923920edc19b1415579b25; original global index 19762.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle fcf963d114fada0e2ccbea693c2e4c26aae518b2bc473552c613f78630aea258; original global index 19770.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

def library : Library := fun id => if id < 49 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))))) else (if id < 74 then (if id < 61 then (if id < 55 then (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 67 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))))) else (if id < 86 then (if id < 80 then (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))) else (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))))) else (if id < 92 then (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 95 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 58 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23040)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 0 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23041)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 81 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23042)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 81 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23043)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 54 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23044)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 55 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23045)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 58 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23046)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 29 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23047)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 64 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23048)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 58 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23049)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 0, 4]], proof := .tail 29 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23050)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 81 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23051)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 55 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23052)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 64 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23053)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 6, 1, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 82 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23054)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 6, 1, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 24 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23055)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 6, 5, 1, 0], ![2, 3, 1, 0, 6, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 40 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23056)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 81 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23057)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 55 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23058)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 4, 6, 5, 1, 0], ![2, 3, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 46 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23059)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 25 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23060)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 6 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23061)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 47 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23062)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 91 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23063)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 93 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23064)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 34 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23065)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 13 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23066)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 33 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23067)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 47 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23068)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 87 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23069)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 70 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23070)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 30 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23071)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 42 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23072)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 17 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23073)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 34 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23074)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 76 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23075)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![3, 1, 2, 5, 0, 4]], proof := .tail 34 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23076)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 2, 0, 4]], proof := .tail 76 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23077)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 2, 0, 4]], proof := .tail 57 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23078)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 95 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23079)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 84 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23080)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 1 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23081)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 36 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23082)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 78 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23083)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 49 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23084)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 12 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23085)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 1, 2, 5, 0, 4]], proof := .tail 69 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23086)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 0, 4]], proof := .tail 35 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23087)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 2, 3, 0], ![4, 5, 6, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 0, 4]], proof := .tail 66 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23088)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 72 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23089)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 79 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23090)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 48 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23091)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 20 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23092)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 2 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23093)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 6, 5, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 18 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23094)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 5 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23095)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 77 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23096)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 6, 3, 1, 5, 0], ![4, 6, 2, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 86 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23097)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 89 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23098)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 73 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23099)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 61 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23100)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 39 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23101)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 89 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23102)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 0, 4]], proof := .tail 44 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23103)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 96 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23104)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![4, 3, 6, 5, 1, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 45 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23105)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 77 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23106)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![4, 3, 6, 5, 1, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 77 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23107)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![4, 6, 3, 5, 1, 0], ![4, 6, 2, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 31 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23108)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 61 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23109)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 11 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23110)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 89 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23111)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 27 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23112)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 6, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 0, 4]], proof := .tail 7 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23113)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 68 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23114)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 53 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23115)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 3, 6, 5, 1, 0], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 19 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23116)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 6, 3, 5, 1, 0], ![4, 6, 2, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 98 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23117)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 3 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23118)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 5, 6, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 0, 4]], proof := .tail 28 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23119)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 6, 5, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 52 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23120)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 6, 5, 3, 1, 0], ![4, 6, 5, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 8 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23121)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 5, 6, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 16 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23122)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 16 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23123)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 22 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23124)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 16 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23125)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 37 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23126)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 62 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23127)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 21 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23128)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 16 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23129)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 85 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23130)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 71 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23131)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 67 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23132)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 32 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23133)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 56 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23134)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 65 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23135)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 5, 0], ![6, 1, 2, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 43 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23136)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 50 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23137)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 15 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23138)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 51 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23139)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 60 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23140)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 60 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23141)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 4 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23142)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 51 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23143)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 59 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23144)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 9 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23145)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 83 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23146)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 14 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23147)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![6, 1, 4, 2, 5, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 92 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23148)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 3, 5, 0], ![6, 1, 4, 2, 5, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 92 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23149)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 90 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23150)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 38 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23151)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 74 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23152)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 94 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23153)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 4, 2, 0]], proof := .tail 23 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23154)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 94 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23155)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 41 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23156)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 88 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23157)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 75 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23158)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 75 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23159)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 97 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23160)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 80 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23161)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 5, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 63 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23162)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 26 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23163)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 26 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23164)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 10 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23165)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 26 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23166)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 10 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23167)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then
  (if offset < 32 then
  (if offset < 16 then
  (if offset < 8 then
  (if offset < 4 then
  (if offset < 2 then
  (if offset < 1 then
  (namedLeaf000) else
  (namedLeaf001)) else
  (if offset < 3 then
  (namedLeaf002) else
  (namedLeaf003))) else
  (if offset < 6 then
  (if offset < 5 then
  (namedLeaf004) else
  (namedLeaf005)) else
  (if offset < 7 then
  (namedLeaf006) else
  (namedLeaf007)))) else
  (if offset < 12 then
  (if offset < 10 then
  (if offset < 9 then
  (namedLeaf008) else
  (namedLeaf009)) else
  (if offset < 11 then
  (namedLeaf010) else
  (namedLeaf011))) else
  (if offset < 14 then
  (if offset < 13 then
  (namedLeaf012) else
  (namedLeaf013)) else
  (if offset < 15 then
  (namedLeaf014) else
  (namedLeaf015))))) else
  (if offset < 24 then
  (if offset < 20 then
  (if offset < 18 then
  (if offset < 17 then
  (namedLeaf016) else
  (namedLeaf017)) else
  (if offset < 19 then
  (namedLeaf018) else
  (namedLeaf019))) else
  (if offset < 22 then
  (if offset < 21 then
  (namedLeaf020) else
  (namedLeaf021)) else
  (if offset < 23 then
  (namedLeaf022) else
  (namedLeaf023)))) else
  (if offset < 28 then
  (if offset < 26 then
  (if offset < 25 then
  (namedLeaf024) else
  (namedLeaf025)) else
  (if offset < 27 then
  (namedLeaf026) else
  (namedLeaf027))) else
  (if offset < 30 then
  (if offset < 29 then
  (namedLeaf028) else
  (namedLeaf029)) else
  (if offset < 31 then
  (namedLeaf030) else
  (namedLeaf031)))))) else
  (if offset < 48 then
  (if offset < 40 then
  (if offset < 36 then
  (if offset < 34 then
  (if offset < 33 then
  (namedLeaf032) else
  (namedLeaf033)) else
  (if offset < 35 then
  (namedLeaf034) else
  (namedLeaf035))) else
  (if offset < 38 then
  (if offset < 37 then
  (namedLeaf036) else
  (namedLeaf037)) else
  (if offset < 39 then
  (namedLeaf038) else
  (namedLeaf039)))) else
  (if offset < 44 then
  (if offset < 42 then
  (if offset < 41 then
  (namedLeaf040) else
  (namedLeaf041)) else
  (if offset < 43 then
  (namedLeaf042) else
  (namedLeaf043))) else
  (if offset < 46 then
  (if offset < 45 then
  (namedLeaf044) else
  (namedLeaf045)) else
  (if offset < 47 then
  (namedLeaf046) else
  (namedLeaf047))))) else
  (if offset < 56 then
  (if offset < 52 then
  (if offset < 50 then
  (if offset < 49 then
  (namedLeaf048) else
  (namedLeaf049)) else
  (if offset < 51 then
  (namedLeaf050) else
  (namedLeaf051))) else
  (if offset < 54 then
  (if offset < 53 then
  (namedLeaf052) else
  (namedLeaf053)) else
  (if offset < 55 then
  (namedLeaf054) else
  (namedLeaf055)))) else
  (if offset < 60 then
  (if offset < 58 then
  (if offset < 57 then
  (namedLeaf056) else
  (namedLeaf057)) else
  (if offset < 59 then
  (namedLeaf058) else
  (namedLeaf059))) else
  (if offset < 62 then
  (if offset < 61 then
  (namedLeaf060) else
  (namedLeaf061)) else
  (if offset < 63 then
  (namedLeaf062) else
  (namedLeaf063))))))) else
  (if offset < 96 then
  (if offset < 80 then
  (if offset < 72 then
  (if offset < 68 then
  (if offset < 66 then
  (if offset < 65 then
  (namedLeaf064) else
  (namedLeaf065)) else
  (if offset < 67 then
  (namedLeaf066) else
  (namedLeaf067))) else
  (if offset < 70 then
  (if offset < 69 then
  (namedLeaf068) else
  (namedLeaf069)) else
  (if offset < 71 then
  (namedLeaf070) else
  (namedLeaf071)))) else
  (if offset < 76 then
  (if offset < 74 then
  (if offset < 73 then
  (namedLeaf072) else
  (namedLeaf073)) else
  (if offset < 75 then
  (namedLeaf074) else
  (namedLeaf075))) else
  (if offset < 78 then
  (if offset < 77 then
  (namedLeaf076) else
  (namedLeaf077)) else
  (if offset < 79 then
  (namedLeaf078) else
  (namedLeaf079))))) else
  (if offset < 88 then
  (if offset < 84 then
  (if offset < 82 then
  (if offset < 81 then
  (namedLeaf080) else
  (namedLeaf081)) else
  (if offset < 83 then
  (namedLeaf082) else
  (namedLeaf083))) else
  (if offset < 86 then
  (if offset < 85 then
  (namedLeaf084) else
  (namedLeaf085)) else
  (if offset < 87 then
  (namedLeaf086) else
  (namedLeaf087)))) else
  (if offset < 92 then
  (if offset < 90 then
  (if offset < 89 then
  (namedLeaf088) else
  (namedLeaf089)) else
  (if offset < 91 then
  (namedLeaf090) else
  (namedLeaf091))) else
  (if offset < 94 then
  (if offset < 93 then
  (namedLeaf092) else
  (namedLeaf093)) else
  (if offset < 95 then
  (namedLeaf094) else
  (namedLeaf095)))))) else
  (if offset < 112 then
  (if offset < 104 then
  (if offset < 100 then
  (if offset < 98 then
  (if offset < 97 then
  (namedLeaf096) else
  (namedLeaf097)) else
  (if offset < 99 then
  (namedLeaf098) else
  (namedLeaf099))) else
  (if offset < 102 then
  (if offset < 101 then
  (namedLeaf100) else
  (namedLeaf101)) else
  (if offset < 103 then
  (namedLeaf102) else
  (namedLeaf103)))) else
  (if offset < 108 then
  (if offset < 106 then
  (if offset < 105 then
  (namedLeaf104) else
  (namedLeaf105)) else
  (if offset < 107 then
  (namedLeaf106) else
  (namedLeaf107))) else
  (if offset < 110 then
  (if offset < 109 then
  (namedLeaf108) else
  (namedLeaf109)) else
  (if offset < 111 then
  (namedLeaf110) else
  (namedLeaf111))))) else
  (if offset < 120 then
  (if offset < 116 then
  (if offset < 114 then
  (if offset < 113 then
  (namedLeaf112) else
  (namedLeaf113)) else
  (if offset < 115 then
  (namedLeaf114) else
  (namedLeaf115))) else
  (if offset < 118 then
  (if offset < 117 then
  (namedLeaf116) else
  (namedLeaf117)) else
  (if offset < 119 then
  (namedLeaf118) else
  (namedLeaf119)))) else
  (if offset < 124 then
  (if offset < 122 then
  (if offset < 121 then
  (namedLeaf120) else
  (namedLeaf121)) else
  (if offset < 123 then
  (namedLeaf122) else
  (namedLeaf123))) else
  (if offset < 126 then
  (if offset < 125 then
  (namedLeaf124) else
  (namedLeaf125)) else
  (if offset < 127 then
  (namedLeaf126) else
  (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (23040 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 23040 ≤ id.val) (hhigh : id.val < 23168) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 23040)) = true := by
  let j : Fin 128 := ⟨id.val - 23040, by omega⟩
  have hsum : 23040 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (23040 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard180
