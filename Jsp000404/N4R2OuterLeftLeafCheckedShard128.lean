import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard128
open N4R2OuterLeftReplay

-- Cycle fingerprint 00446328f21b65e6f6873d3b2fac6b107cc28a0591de3007162de6ab2b677472.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![0, -2, -1, 4, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 19 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 0061eb0e3c1f4123ea43847e38e6a0691ccc32b692ab51fb001a0efc660824f1.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 028dc305099b46b22f57bef485b56fe38b4307d5e49dacacd9ad5057c34c5de3.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 04361aea62bd00672e228fd0252b784eb2e61ef2e1170a921db1c3c6c414e81b.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, -1, -1, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 04774d33ed124162de37a7811280b3f6d760d48de7e8b612bc1e14c64d71985b.
def localCycle00004 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 0553e6a250a0b8710e1005f9a16103d2e07f53e389249fb8c384fe1f61688dfe.
def localCycle00005 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -2, 0, -1, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 07b27db64aaf6930bdd1752d942a0fa86d5b22802964f29dbd22f9aa944dc865.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 3 0, .triangle 4 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 07ffbcb149b7c051c0b2e01b2c09854c3c53a2b5338c5ed8a010ec7752e49bbe.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 080b5f81b30a0225d14f90355019e792e9476dc3cf92c3f180d2474d1ce1e37e.
def localCycle00008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 09dab59f140e155860473c47a98c355e9b171af397dba8820912ddbe6c88af01.
def localCycle00009 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 3, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint 0ada2e0402e50fa494564782fb85f8df91bacaf425cc85ef7ccf193cd865502d.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 0ae08331ed9e601d27ee63c759c973225b978b261c5e7585d76866848693dce1.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .triangle 2 0, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 0b34cf70e6a581cd2bc4da75f6236d448d022e222d6ffbbc591c88bdad38e1dd.
def localCycle00012 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 0 2, .gapUpper 2 4, .gapLower 6 3]

-- Cycle fingerprint 0bb3438291de0d858efbedb7e33a9856b696cc5e588a2a2f3e43632b0b24b2e5.
def localCycle00013 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 0c1f035cd17a35f72f57355e2b6b1c7d248f91972989a142bdf819f15d152e93.
def localCycle00014 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0caf1e555c357292880dd30855a9d2d7967de32accf601262ac15ec1c632eaa1.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -2, -1, 4, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 4 0, .triangle 23 1]

-- Cycle fingerprint 0cc30ff7c8eada0ed8d2ccd17062439deedc163a2cf71a52f328de9f347e1ad3.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 15 2, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 0cd13220f27705d99b179aee56dafb3fc6ac19c3caf814401e78ba38785c7999.
def localCycle00017 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, -1, 0, 0, -2, -1, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2]

-- Cycle fingerprint 0df1d3494358afd787ee50e6b97dd16a0a835aa07e1697680528f45c4bc7a088.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0ead6ef34665e7addb627758cea43e1ce82aad56a82112bb9b66ee20dcefed49.
def localCycle00019 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, -2, 0, -1, -1, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, true, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 0f3478d4e4b2fa91a35970ae3c57d2b7682bf8e10170bf0e218327724b78b2e6.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 113976cca12c5634e9c2564d3930a3bb8918bdeb006d86a9ef84b5542f787f80.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 121d94963273d6d36b4e0a05d98d6105c0a8d7c2e343d888d01f11f0ba31ebb7.
def localCycle00022 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 14cfc07102307b063e1f25ae3c9b922d845c051ab6e36fbe7cac21e5a0d41286.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![0, -1, -1, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 5 0, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 1583a86b3484ecf3160d6ec7b95e9d231e7d0833168b0cff440c2c9f276ce469.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint 166e7331ea26acffdfb7d6b0ec3d3ccf8b965ff6039e95264a8d4e4352928caf.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 4]
    constant := ![-1, 0, 0, 3, 0, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 1745f4525577a8ea0497d847498dcf1fb6d25b0764e1dc54b034e6cd2638b8c1.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 6]
    constant := ![-2, 0, 3, 0, -1, -1, 0]
    coefficient := ![-1, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 2]

-- Cycle fingerprint 17fc162a0de19eaaae39a531dfbcdd000bc2743577007fdcd0515b3304c2b2b0.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .triangle 4 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint 1824260135af2b95e66ebd368603dea05f0cabde102e09b41a83967d32a1f546.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 18e87bc0d9229d025f553b6f002f67f3dd9d392e94edc586bf21f328c0f02b47.
def localCycle00029 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 19db6dd7c1e614fcac0db1bceb5759fdab5c5401e3dc84591928e930b59594cd.
def localCycle00030 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 1c63afc9e5fc0742cc04d51c31023c05159c567540a6fee69c7fe37e604ae75e.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 1d67e8b79a695c243455c9deb05e799d3380b82fed2df4bb3f02d558cee353b3.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 1d992d51d56c2075dd9a700476b4be90752d8af6bb380444599c287c155a777b.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 1de22bd3befe57be4240aa3d962556de024545b07004e8265f0c03a3d3a3b004.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 1f123e025952cf20a9365b0bcec5fa35d44437591c00c720b36e5c5c9b822cf6.
def localCycle00035 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -2, -2, 0, 0, 3, 0, 0, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint 1f4d02b84d757b43b0c0b522e428351e18075068c678807b44d0be9c3a63f6a4.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, -1, -1, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 16 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 1f6384f8e98a72c018540d628d750bff34b95312a9572cbd08a5feafe980fbdb.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2087218ff811b62bf0a1b997503ea153bc7155a81ea56c0022a2ab2f0578fae1.
def localCycle00038 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 1, .gapLower 1 2, .gapUpper 3 1]

-- Cycle fingerprint 20bf3307e2560120bef6a44c6880bb31b1ee3364a6892c383135f5ac26f40e95.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 22156bc3871a94fadfc49b3cff5e42c973b55668459d4de6bdf5064eae8c29e8.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 23c50e0ca6334ae0d9fbec1f73b4fb6cc191381e961ef9a09bb0e2e33fbee1d1.
def localCycle00041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 241ba8f3f8fd9de2eb2f42f05fbb23dee211ddb101a7006e0657b62fb588922e.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 1 3, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 24724d0d9356d585f5fa7f85b2da572f0b88ea142764497849c4855bfdbc12d9.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 2554fcf0696b97e3717faa7ab2796e2a68c4068ac299705ff528ef2c44955071.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 256153ac178741159607325e53696d11ff8f07791112506f72b9823b4f274e36.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 25a3f21687b515ef2667109808f6be0ef76c04127124b85a77189ebefff00a79.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![0, -2, -2, -1, 4, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 19 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 25deda71f7b7b0f3b362b3c9755898a93a56b44d8890a92191f58754e9967c8a.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 2662dbacc51a1bdd4a9bd734b38ee9898b81f7c37cfb78b859c89bb205b16109.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .theta 1, .distance 1 5]
    constant := ![-2, 0, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6]

-- Cycle fingerprint 2683c003ae4eebe388133237d83be2e745d015a0b25edebe7d65d9a430818ba0.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 4, .triangle 21 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 26c262b98aae609830657c3ab6f662f58d02d92e4a235d0a39ef4c05da35638b.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 2778d03374050d8e3e3de459157123f990e4f857fc42c979575df2b35a0d18d6.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 15 1]

-- Cycle fingerprint 2a36603cc8edc7593a8fcdffc190ec1820a823e4d8d4ed5dc14444c6befa4480.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2b4d8ac667e2c34a6da75f0c4357fbab6db8f91bdb57a84ea6c21f06f2d1b8c9.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2e14af2eff568959343fa532f42eabad62ce24f762d01859950d5e38f4b8237f.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 2e7776766f47d53aa7cb9eeca8b3df8d7d9810d873745a45f1fc687ce69340e3.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 3, .distance 3 5, .distance 3 6, .distance 2 6]
    constant := ![0, -3, -1, 0, -1, 0, 4, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 2 0, .triangle 16 1, .triangle 15 0, .gapLower 3 0, .gapLower 3 6, .triangle 33 2, .triangle 27 2]

-- Cycle fingerprint 2e79361a3d84ae460659a88622c083d5c3675c78501995aa5439732dc4933b0c.
def localCycle00056 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -1, -1, 0, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 21 1, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 2f0357e30200d305b548ff22ca42375f6b9076d8a3f6b57e9aebfbb02c985480.
def localCycle00057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 2fb213791107d2c4263acc834b07b3af567ece320325e2d224aef5766073fdbe.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -1, -1, 0, -3, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 3023352f59630a251c734bb7d6745388a598db94c2134841e6127b833471a34b.
def localCycle00059 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -3, 0, 0, 3, 0, 0, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, true, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 303dda38010e97a6300e6f713426470514c88dd17b837e1ca72c929a8737bdc7.
def localCycle00060 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, 0, -1, 0, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 305f120b12af48d5d806352f9feb56321ac072f39111244deb32013674828c8b.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .gapLower 2 3, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 3061cd84517185cfe1442884fd8c2359c03ea01178b6ae2f8296338e0ef5ab83.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, -2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 314c99d03f7be32bb91bd807ec54e5ab2a0db8bfadc1fd955c25c28b6d66c5da.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4]
    constant := ![0, -1, 0, 0, 3, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 23 0]

-- Cycle fingerprint 33c2c06dc6a68d0a341c292ed00b778a43d1e5c13520ea1d442fd6c4215eaa73.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 346833298e8e1a15c81fa843e3baa36dac7974f5cee35f5f34247fda7e5640d9.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0]

-- Cycle fingerprint 356bfca7a5cfdec731f88e40c7dab6a82f91ccd70ea834e7efbce75178bafbaa.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, 4, -1, 0, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0]

-- Cycle fingerprint 386ca266c1ce95b6fd679da3d781851f25f376539e7cdba3851643aa1e21b494.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 1 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Cycle fingerprint 387b226a73ed8a2c1ff6693bafb30f9dbb1f737a94231c2a97e77ab2e237cff3.
def localCycle00068 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 394ebcdffaba112879738f66fa9457797fdeb9b27f301b36711ff3fa1badce2f.
def localCycle00069 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5]
    constant := ![0, 0, -1, -1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 34 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0]

-- Cycle fingerprint 3aaa68a2924cdc9ead15c907738d51bb8357bee6cec21ceb2e22a88b93732815.
def localCycle00070 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 3bb162786982eb1cd10ebfce8c8e8b5dd9843806a9db897009bb79a745b9a1e1.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0]

-- Cycle fingerprint 3bca4bbda6999a60d5689f196cc83849ded3857c25d8ac810d06124373a87516.
def localCycle00072 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 3beee8889fed02e5e6ba9701489db9fbe87a4f219b43a497748d87c837f331af.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint 3cf896383bfdb6afe859a5579988366b77a074fc016309ce257be9a682b35867.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0]

-- Cycle fingerprint 3d78f08829d1d97661c3a9efa6b6fcab10987f29a43fce34f936c8563b7c6e93.
def localCycle00075 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 3deb092e5a59414fd1d0705419d36b5e94346332044c80d2f3b481afe24c24a6.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 3eb35e3517e0c635d3e2171ec722c472e127448c0dce7804033403a4c208ac83.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, 0, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.triangle 26 0, .triangle 33 2, .triangle 21 2, .triangle 4 0, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 3fa818b812e5909fea3390ef9b6d2bcecaeac57609737a0f536143774b374fc0.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 20 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 406a08661b4a9ade3adc6e1f19ef83e179b013988e470a452f98a174c611f107.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 40b8c4d4b0cbb97b5a84250c7036712d8c202f0beb2d225decc2b184345d0fe5.
def localCycle00080 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, -1, -1, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 41a0c04e3fe651b2c9e1da018e54d6991c1e1c51fcc7e0aef5cd68d32c073bd6.
def localCycle00081 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 34 2, .triangle 23 2, .triangle 4 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 41dec66549e0524f171aa90b52fd40c35aca2a5c0ab8e7eb1a80acbb52cb7ed0.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 42523987ff73a2fb48c05b8bad0ba8ea21998730b5ea5ef31a7f5c8c38ae12d3.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-2, 0, 0, 3, 0, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 446a476536296c78c4755cdefbcd6634f4dfd915dc2ed2cc308192d68e228d5e.
def localCycle00084 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 447a533022ab8bbc3d5ca9b91648e868c80f1b789b3798e7f4db0d3159f23db5.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 455a2ba1e609373d446df8466f6975bd745814437dc1b68b0549f69f91dd5225.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 46b2680c5c546292764c34874703c68ad9f8a083843ef42f97af8a232ed88c2a.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, -3, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 34 2, .triangle 23 2, .triangle 4 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 46e79890895643ee018594458cb6ea3906185bd8bf9600af085a6886629ded05.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .gapLower 1 0]

-- Cycle fingerprint 4953728c16c54727eb995a61c69b95f7ed77b3f8c3ba73a9957cd01a84635cba.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 49e0b2ef8401a2804ce90f104119ee07cfd5c84e1322a652a33a1cf8a882f994.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4a8d8b958fb384d8bb5ec5cb31cc34e85105cd41179888604eb981e7375af3c0.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint 4c81395148c696f266456ef198cbb4b2165d90a932d08b159e539b5b99a80f2f.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 2, .distance 1 3]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 4cfbf4bba178c9039eab47132d0a05746c0ad7bba9e1d8554bd6ba2f01719129.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 2]

-- Cycle fingerprint 4d49e616d9546bf217ddc116d6dea5f2b0a88acb55090563b1967134e2a41d94.
def localCycle00094 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -1, 0, 0, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .gapLower 2 3, .triangle 15 2, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 4e8f80720857c5d3b7d569ade37d2512c1166dcdf5ed5addac24b17bf4a19202.
def localCycle00095 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 4 0, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint 4f816f75d6842f244897beacce3d43a642d90513ce727d006a1b21a669e9df10.
def localCycle00096 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -1, 0, 0, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .gapLower 2 3, .triangle 16 2, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 4fac4f9d9a58fd03ddddd112fd0da999e59c9ddb472239ee4476332c88bdbcf8.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 5016e2e6a9a26431107d62de22c33abe5bafad6d283b7322f1f874c97bd3e391.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, -2, -1, 4, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 4 0]

-- Cycle fingerprint 51a8eb8314b8a4cea34e54bc94a19f20bec738c54be13dab6a867136ed88478b.
def localCycle00099 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 51adc29c88b319ef695bceb89ec2a82bfebe9ad1af6831b9f8bc3ac727f15592.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -3, -1, 0, -1, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 5377eaca9868ff7fc3d3a3c4745bbc36ffc677627eb35bd85ab18adfb5c5b9cb.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0]

-- Cycle fingerprint 53fc8f1865f0064eb386a6948f1f33c63b3f32062d0604d7351f67dfe7186b7b.
def localCycle00102 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .gapUpper 4 0, .triangle 16 1, .triangle 15 2, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 548f59be31d9609045bf1d5b5a1cac734e6c3e4209291db2a5a5661c4c27a5c7.
def localCycle00103 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 55634df2cda92b5e64c0bc9e5266c42b7bb396a9b0ccd2367678e9900b05fc25.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5566b4b3e4079c1fb2aaed84ba9b7ab5e41fd55b3561b719431226fcb34bef8c.
def localCycle00105 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 55965438da2d01711469c0f9db3fd4da47a99380f151d867e0af4e1647afd3bf.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 565b9bbae4a6a27c0fefd3eeaf397d32c6d5ae0950496532803d3a6475049c5f.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .gapLower 4 0]

-- Cycle fingerprint 568339e20d4229e9995d4d32c60fabf79aef5933901a870b954877558786a990.
def localCycle00108 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 18 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 5729d45d736f69d002388d394b48e94dd4c5ffaef992469b434b3453ced43836.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 23 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 581180669f52515d0bf67d30a008561076c28f5c1da79c5d5d98dedac82f6af5.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 10 1]

-- Cycle fingerprint 584360cb3d8f3163b2ff4d12e135d6c04718f303ee8cf7ea764d22ea276e95aa.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0]

-- Cycle fingerprint 58c2db35760a068743169775cd5c0d7b00c5957cb21074fb918f291cec290add.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -3, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 590b7be88c1657cc19c55cfe790e128e2d651c53e0d9b5d0aeca55950cd57c5e.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 5a3551872679c8d463fbc99fc62a44c114dc009e32ad4fa8dc6cec98b0d252d8.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5a9d6477393738be240a9c4d514aa3b4ed264b1b89b0b526e1e8273e1a8b2db0.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 5ae87f17cd2f8664b3447d2e76bb491414d6148c398d7a8ea8480d87806554da.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 23 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 5c67c78a257b2bb8eede96ab6940cb491fc2010546febd3e0ae6b68f57d4078c.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 4, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 5c83be952167af19a2ea8272dceda2c771032e74f556b4e25dcc65134bad9906.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -2, -1, 4, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 4 0, .triangle 21 1]

-- Cycle fingerprint 5c94931e71fb001eeb92d0a362a035f889280c4606b9b3aeebc3218b3e0d2697.
def localCycle00119 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5d85c58ffb5c53ed2f6d829878700494ebbf27d9dee705c7cd5a607fbcc336da.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .triangle 19 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 5e483770dca96c26786a95faafa6bce4bead7cf587e8873d2935972d9ff3e7d9.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 5e7e267cc15200ec383b50cc017f3078ac27b44eab71691532a08290d0fcf8f4.
def localCycle00122 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 6019e15f1886865fd8a8b8a9327c8887661adf3578a8458cc6daa7f0bd97fb03.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 604ce4a2e958af3a0f679c459326621fa8df44ffedb34cd382acdc2aa1f99977.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -1, -1, -3, 0, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 6085e1046c9fd966b1d76e80ca152dcc6a96995bff45f9dc8786a8326db32567.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 60ad61933c866eb9750b13fb425b812f35cdcc8b21f93e61c30ba612ea7ca835.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 60da3f933a4a261107f5dd05b8cb64015efbdcb5016e217813172fe8418dd8eb.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0]

-- Cycle fingerprint 610c16bf824f7c065ea324050076851bf2837bb8c7cb1a2ae844c394e16929f1.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 614be71e18f1fdda26fc02f773e8125d470f4069475702305e7d4f06203f29d1.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![0, 0, -1, -1, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 631db1d5f4ef05f5e933d906de2ffaed9bcc59bb063c4cb697cb1e9bfcc87060.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 5, .distance 0 1]
    constant := ![-3, -1, 0, -1, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .gapLower 2 6, .gapLower 5 3, .triangle 3 0]

-- Cycle fingerprint 634e26b52dae82119fde840ec23fe1c4b75df72ebda27d4ff3146c8a524b49d2.
def localCycle00131 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 21 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 635084c1f6ae230a1b3f53c303a819882943e41b27807709b6d632b1d7531863.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5]
    constant := ![-1, 0, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint 63d34658895f0b57c6fa3fb8b9b133000eb0ea43e1453c03a0efde11fd078b2b.
def localCycle00133 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 64536454baecc73ccdf416d47950a8066a7510b41175c42d45ee575223870b92.
def localCycle00134 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 65a3663f9b67e6e6b6acc7cf37a5ed700a12d36edcc62198dd2bd7cb98512ef7.
def localCycle00135 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 0 0, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 65d9d7dfa23c1901f2a475ac3228370706b5a6b8bc0928ae016602f45d4493fc.
def localCycle00136 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 65fec6e8bba57b7133a04d405dd427c9ce02d08ae044ca2b2e25123834e68edc.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .gapLower 0 3]

-- Cycle fingerprint 666e3d839e04291db6baec1c19afbe78d58e9027fed79153c00fb48ba8f3bef3.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 675a9d5bc20314626d76a22e81324ffe125f564183b2987520b394ba47bf36a4.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, -2, -1, 4, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 681743d90f3ad6543f33daadb08b3fffe28821f17fabfae3bb964b56717e70b6.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 688126b7087bafdfed600a76f33265b813c1ccfed3f137c0d99521bb5aa2a309.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 689a5645d6b2ade22c5e32e0ad4328eda9c35401f53333aae543db1506c3786a.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 68c9bf22017a1a28d4e71be22a138bce253767bc8a46445e4411e5b3f2ef7e20.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4]
    constant := ![0, 0, -2, -1, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 6 0]

-- Cycle fingerprint 698313b21102abb9b46619179b695f1337ac7eb024b88d958452c247c326ad27.
def localCycle00144 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 6a3153c75c0157e0af04f49652c37d8fadb5280815ca13dcf9872cae83be3125.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, -2, -1, 4, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 4 0]

-- Cycle fingerprint 6a4e769a7069c0fb32b021baed8b09e24996d714608ea5742e08ba0d99b21e3d.
def localCycle00146 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6bc77348da3fe1af3c154f4fa865ab6e3aeae2d568daa7bf5314141979598a14.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 6be31b4ba187e36e77fc72a96d65ccda104ea923d437b317d481a887ad2f8a0b.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 6d424bb0fee793b3b1187cf5df0a4f72bb7f4bfca93fe29009b4a3fd08a1bad4.
def localCycle00149 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 6f5208c20dfc27cd2c1adf19738167c95c00f392c3135f698593747b7a54b365.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -1, -1, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 6ff943782b2d9cd7c599b0530a6460c5dd6e102cffac209933667dfa022a73cd.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, -1, 4, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1]

-- Cycle fingerprint 7041fd9aa8cbb21d78cfe03c0391bc6336a4dd8c0c0c6aefbd85dc402454f1ce.
def localCycle00152 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -1, -1, -2, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 7068e7d11e2437ea2509a5d9f493983d3a5a30699ce44d8c7eb2244a69b78dd0.
def localCycle00153 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 70e424f604ca9a68642cbf4facfc5c0e47038898f6a48c636cca39df80e34d27.
def localCycle00154 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -1, 0, 0, -1, -1, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 71605fcab41abb9cda5b67051e57dcb398a6412dc427e1f9597be8da63c054c4.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 717899c9981747b0fe5f642a4280aed0261fe6a80bf7e119bbfe074fb3b9f34c.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, -1, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 73a2b345f68d0d7a12a146af93d39b25ddfff7047ad5259be7d89655394b7463.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 2, .triangle 5 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 73bbdea7893c1e5c1e63358b5e5d3d784d20e4091e0754784b552b62bdd21bb2.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 74d8af470d0e089861488f3bf8ec5e214464d6ea8a28595e375418dbaf78dce6.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .theta 1]
    constant := ![2, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 5 0, .triangle 15 2, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 7535166604ce03089d7bb36846d44b60de7526fcb2a3221c3309a5b6ad23abb9.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, -1, -1, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 2 0]

-- Cycle fingerprint 766c53533c54225b433f2161c5f6499bfcfc71bae0b9ccd7ad07eaf688fefd78.
def localCycle00161 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 782b15c0fbfc81b481888dc3bf68136a085e877cfc562d212ef9550806b539d3.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 794059ae8ce76acfba11c0e9341696263fcde1249ef8241041882890aa3611c9.
def localCycle00163 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7a140552a0cd738ab86447dff23d256780dc60194e2e70b1b47ff9d57d0eb523.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, -1, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 2 0]

-- Cycle fingerprint 7a6e2296f50b592faa336f2f5d3b858e7d7d945ef1c678978d4a30c175df7cca.
def localCycle00165 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 7ae8bccb7c2ac2a0a76e3b48be9a02892aafaac2b0640034f913aafb9125dcda.
def localCycle00166 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Cycle fingerprint 7c007e5347a18fd61fccb16954841957f9d3e9325ee25d4f86787614af218e44.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -1, 4, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 7c8ae13e504cddefeb916fa565142fd79571691d6fc2de34b4ccc4f14ca205a7.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 3, 0, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 7d0119dc047f80df96fa9e6c573a016bd382f76d3ad027a83918cc1f57b83ee6.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint 7d0a6b5788c05251575c5bb94382e4eb86d013945920aa776a5f40893395d2bc.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3]

-- Cycle fingerprint 7d7a1c8a95220fdcafb2cb2e196d780b9698413d661e8b1cb290d6cbcd3843b1.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .triangle 3 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 7e505ade9c449b339fb490ef9b63ebe8dcd59284a71f4f4f761928a66ce52793.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4]
    constant := ![2, 0, 0, 0, -3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3, .gapLower 1 4, .triangle 0 2, .triangle 5 2, .triangle 9 2]

-- Cycle fingerprint 7e71170e0c1ca823f1a226e305b0cd80cdfded605d2f5a0ba75d1f0597158002.
def localCycle00173 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 7eccf882bfa3f9757ffa3129ceaf4afa9431a30fcfce99ae0ce5545455c64a8c.
def localCycle00174 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1]

-- Cycle fingerprint 7f68c3efb0bf5e628cf01543ba9d5d6fc76849ae2b6e4dc53c6a23a751531a81.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5]
    constant := ![-2, -1, 0, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 4 0, .triangle 23 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 813d7a5d77e27394a7df9e93ddf6a98bae6432f55e3c4401ee76d50d9bb233c9.
def localCycle00176 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 8272a2e89f54448aa3b3bdcccda687b2718601ac2025219b0fa7487add3d1dbb.
def localCycle00177 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .gapUpper 4 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 843de597864687bb5c3098668a5ab9f5e316aa4640c884b8b17eac130ee5172e.
def localCycle00178 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -1, 0, 0, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, true, false, true, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 8447acbb83d834b56bc792c1d41fac573915d2548eadfd240611138bcf148d38.
def localCycle00179 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 8515b0112e8e7c24b483b13440ab0116ed9591ab071d3ed03d6ff9694aca0c12.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 8538600f852fbc2f2c45c58b77d36a37feff79315f9fafa8a7d86f620f8bc6dc.
def localCycle00181 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 2 2, .gapUpper 4 2, .gapLower 6 3]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00182 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 86cd4278404aff50ffd6eff03e65839988621734c1a5bb70040c2a6b03da6948.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 3, .theta 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 4, 0, -2, -1, -1, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 0, .corridorLower 2 3, .gapLower 2 6, .gapLower 5 3, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 2]

-- Cycle fingerprint 86fe1db77edab10824474c3c987710d1d2958adb13a4d7b89fba4b15612b7d0b.
def localCycle00184 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 87c4d7e0e2dfd8e1be341d76056725be840cbcfa3d13b257f65d14ff02cca18a.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5]
    constant := ![-2, -1, 0, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 4 0, .triangle 21 1, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 884bdf49ce9ab66bcf74876bbbab9155e2b4e534787673ef8f0a9df17e49b300.
def localCycle00186 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 88afe315bd5f5fecc041461daac761979eb25515d8e7f4f2bd8b9ca6957aabe5.
def localCycle00187 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .gapLower 1 6, .triangle 3 0, .triangle 4 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 8aad2aa49f7141625f34d2dea688c8e56e442392ce4b233d307ea5f53e0d776c.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 8b874a3611f1c66e3e98899a3b34cf65974bcc16e9a56394a2c6ceb3ee5c58d1.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 8d37d8e74b62cfde3bbc9e065d0276ec2036e346ace6d862906c136cfeb02633.
def localCycle00190 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -1, 0, 0, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .gapLower 2 3, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 8d54e9caa92e08518c40c1416c375d03cb4ad1ddb806f789565439b6e20bbace.
def localCycle00191 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 21 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 8e85119997f09acba54ec98585f3da25034096540ecbaf16853d600699115e8e.
def localCycle00192 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 8f2493ae2483afffc1bf6cc698cd18b768fbd89fee3d64f2ff2aebf1098d5ebe.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 923e85425ecbd39e1c1a186377f08321557b3466388ae6931666efb0bcc1033d.
def localCycle00194 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 93bee719ca1b1e8535ed68a0ec34738732c576fda69a9d9ea3cb2461c10ca9c5.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 21 1]

-- Cycle fingerprint 9401df9f55a7e1dc97343f310fc54546b694684a2f69801677109f4b9f176781.
def localCycle00196 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9450cf65a8fc5ce2f64e9b2835240cc8e73d15433e8598dae802616c5bcb18c1.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 960f0871b8bafbe66f4aecb2d37a1f935d720c46f73c6de08cfc80e60b979af8.
def localCycle00198 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 961fb927837532d0ac53b9b844cf05ca7c631dc69e09aaaf0ffba0ef5e5260d1.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![0, -1, -1, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 962c4227fb339bcaf5cd39af1146f1b332a37a22288c2048f07857b97e5945f9.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 0 3]
    constant := ![-1, -1, -1, 4, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .triangle 5 2]

-- Cycle fingerprint 96cac80784edc9f487e1cf7d9ba438351ce24ad7422ea3892a68fd382d7f690c.
def localCycle00201 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -1, 0, 0, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, true, false, true, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 16 1, .triangle 15 2, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 96e99b8e9893184aa35e0f452b764efa1661617418a5bbbc12b6e4f542612dac.
def localCycle00202 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 987cd865b2f8e5101aef39c932bae36743639d12a54773485805675c2183f73c.
def localCycle00203 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, 0, -1, -1, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 9890febb1b690c1fe4187548d9080aa8e14c2545f3437ade32b195112b6de391.
def localCycle00204 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![0, -1, -1, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 9913899f69b16404e6dfb768bd9a388a0a4aeb999a32e5aa5edce169afcb1788.
def localCycle00205 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint 996e74de54e8690d1987a3c29060acc2903341a5aefa2a66a344100038acffcb.
def localCycle00206 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 9b95dd31f59f7e11f027d26b77947e6943961a0d9e487a12fc032972622ef5b4.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .distance 3 4, .distance 2 4, .distance 4 5]
    constant := ![0, -3, -1, -1, 0, 0, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0, .gapLower 3 6, .triangle 25 2, .triangle 28 0]

-- Cycle fingerprint 9bb84f8118c12f0668f50e3fbd3c6b3c6c9e87023e816d2ba167d3849e91614c.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, -1, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 5 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 9cb1dc10ec5018a215232c4decccd31e733b3fe6ecd5918078fbdab0349dd53a.
def localCycle00209 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 2, .distance 1 3]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .triangle 15 2]

-- Cycle fingerprint 9f3745de39eb1eb7d4db9b8e012cb3e7cf2b8bf1448e36ca1d32f785db9f9cdd.
def localCycle00210 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 9f4b796ff12c57c3ff25a39ed6bec8881ba9e1ac5f9d339b2e906ee9cdf219aa.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 9ff3421251f299d11cc925cdb3537be5065bdb7a56301d7fcef1269c1ffcf4ba.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -1, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, -1, 0, 1, 0]
    strict := ![true, true, false, true, true, true, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapUpper 6 6, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint a03c3cc1053a277a13cdffa9104724a534b136293632b1e969616fcf946080c9.
def localCycle00213 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint a1492bbadf818daeddc1e3bdc5afe6acf631c1243e4e7ce81604dfe8eb403744.
def localCycle00214 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 18 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint a25f8b465e93100807566bc60683a35df4bc0d02d979f9c10a508487f5a14e56.
def localCycle00215 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint a3fed45771d2e7e2bfd7ecc97b3533275fdee736c14de07d0e86301585acd70a.
def localCycle00216 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, -1, -1, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 21 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint a4b432cb78149fb16cd906b37e47db4504228e88ecb2068477f40e566e1cca7b.
def localCycle00217 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint a55c283cf3937043656c90f3cd2e9478acb1cf8a9a666124c7b8d94491a44d2d.
def localCycle00218 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint a5940926ea7e96cbe499d2a233b18fc636b624a086dd25bc77cc761b7853ee34.
def localCycle00219 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a63cbef1d04b2d2e75a6f9c5c5f39b863572e3b9f355e3662f55377dccbf0b1e.
def localCycle00220 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a91dab2d4119c8cbd7414bc38152bf5e8abed18db674f262c11da543834c0f35.
def localCycle00221 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 0 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![0, 0, -2, -2, -1, 0, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, false, false, true, false, false, true] }
  origin := ![.triangle 9 2, .triangle 2 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint a9b59b73b165d9afe720d58831606299d54ab62e9a4c0000a29acb1302ad95bd.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint a9d89d3e4f57aadbc617228cbf3d014679b2826577fa200f217ddf4970733075.
def localCycle00223 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -1, -2, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint a9f497ae6688a8c993a55d0dfc75a74eaac053d21a4be05f21743be0fc8ca3ca.
def localCycle00224 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .gapLower 5 3, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint aa700946f71529441e7f407a77280d605dce4b300d6fb5f9f00ab22c55c757a9.
def localCycle00225 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint aac7a930d75f8b53b4a6876011ac141d0e2095742740740e39f6276c6141e858.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint aae881bc1525f5ad9581e2c4eeababaa93ecfec505ead4424d80d253f04f2a97.
def localCycle00227 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint ac52088406b17996a5bdb5804ef4a8727316056eec1de7ab4052b6aa4f83a81b.
def localCycle00228 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint ace0d4047d90b79ec0964d019140b394e61a7da8b23e5650b2357215ce954489.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint ae1440d3aa981fc4b845e59b25ed1add8fd186388c6cad8dc6d93dbfc78d0536.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, 0, -1, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint af8af8b39d50c929a0ed72a30634403793b9296a7ed2e90ebc0f0c18b3cdd353.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint afb3de3b552effd26ef10481c59c691a326a23ab0d22387f1e8bfb2a948aebc1.
def localCycle00232 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 2 0, .triangle 16 1, .triangle 15 2, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint afc6b2b7bb0d41a4220c9e66a7250b38dcb78358ed13a7b1b4dd4d5c13f95de2.
def localCycle00233 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 2 0, .triangle 16 1, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint b00224486d99f05f98edd719c00f7646d9b53e0f8a4dca569956fb95286114be.
def localCycle00234 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 4, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint b02b08d39d0a5bf869792b43ffda9c3ba0b9796389b1bedcdfc590fd670ba593.
def localCycle00235 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint b0b3d53ab8f2479911d452ccd1154a1bc6bc7dc4767d1a9bbd89b117d9950d88.
def localCycle00236 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, 0, -1, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 2, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint b0ca1e732fad089d0fa98f1b98a20da7d119e1e9935430e666f80bc5be1dfd54.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, -1, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 0 0]

-- Cycle fingerprint b1056fe8b66b5c25a6ab8d1a6f2d5733767ac7c4864b225843f2c042767cbfb6.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 18 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint b10960077dba1275a136abe42965ac09d2dab06a5744ed99947b5598419d15de.
def localCycle00239 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, 0, -1, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 2, .triangle 5 0, .triangle 15 2, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint b279af9a3ebb0d6093de5d568946362b2779c4b97ead6ec4c1df7861a66e291d.
def localCycle00240 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint b2d4a04c56d30dec5b2452bc8a428447070d37947195472c276e3e2bf1aaa171.
def localCycle00241 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint b30972e96838eb4d3abdb93c4b3477a1aa1cb6c11f3b1f147ac342bb4dc9debf.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![-1, -2, -1, 4, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint b4f1d37cd9e7f78f819835656f46a585641d1ca41ec6a087f3e5723e2c50ba59.
def localCycle00243 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, 0, -1, 0, -2, -1, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 19 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2]

-- Cycle fingerprint b5972941a875f207e010a72fa22e4b69a2209902d1f1e1deaca9087d23d3a381.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, 0, -1, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint b5b646243293e66f56ba5831b715de236e89fe912104231fe1a3498351a65604.
def localCycle00245 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint b6187ef53ea8f036ff9aa82d1fe4e75d058ecbbf4c8209eb19c1c7b81b33ed2e.
def localCycle00246 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -1, -1, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint b66e8267c5d42b4520c2afad4c655f17ca8516755b280d07ef0ac16a71740a3b.
def localCycle00247 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint b9fe264b9192c148908d0b6735c425777e5f6262ccaa9530ce3c30708f567776.
def localCycle00248 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -2, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint ba1f4a80f558c4a698d7e586e50f1a0d85062f7363f78d9c6bce3336db2d028d.
def localCycle00249 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 1, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint ba6a545e2ec535498f8d112343d235e84c63c42aa6ba17829c76bd7db955af79.
def localCycle00250 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint bbdc3f78d16d67241b9e4813674a8686286243f269babc08b4d3f5cd6fdd4562.
def localCycle00251 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint bc0a3526befbe9f28411abba55809a9aaadbe35c6196289ff9acf1f22e73810f.
def localCycle00252 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint be013e17f62ea52048835b2411c7c4d927b4c734623bb32195c3974515b79f17.
def localCycle00253 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 24 1, .gapUpper 5 1, .triangle 3 1]

-- Cycle fingerprint be396ed2ec1382acdc717b986a45fad6045b5d20846cb8f8c319f147707694bb.
def localCycle00254 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 4 0, .gapLower 0 3, .triangle 5 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint be986cc5bf8ea2e8cc472a076b7109104767ac9d1082dcf3122564e7c8617b07.
def localCycle00255 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .gapLower 4 0]

-- Cycle fingerprint beabf3b8e5feca01afad33080ed479b52366481c775d078917c67f719e80572f.
def localCycle00256 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 21 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint c03878086b61e07b881c64a6515f0251999b273ee6ade19b4ff3ea6e1f9a1f9c.
def localCycle00257 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint c04e2ef526917baaf95b717a2c67f16c807db6911bdf8ea750acdc9f61c1f40f.
def localCycle00258 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint c098f829885493d83ab78f2d2ca3ff735df2f0ab459ed7d2939c13765006705b.
def localCycle00259 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .triangle 3 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint c1a112510c810c0632c6cfc0d8df497d6180cddd9d6a989055c7ce9bdd5b9e5c.
def localCycle00260 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint c2412b125075b340099c10309e2f997dbbd556b126e9a37b508c5d53e0046b5b.
def localCycle00261 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![0, -1, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .gapLower 0 3]

-- Cycle fingerprint c26545d52cf01cf6591962c8fec1eef561b679df0a193cb08db3790a88974c19.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c2f5b70387d7274796f9dd4fee04b71a6ddbea70145f0d3c3589180efecc410e.
def localCycle00263 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint c31cceaa446a63f53e6ef2dfa4c3233fb9659328c37077eb9fc4c9582afa2d55.
def localCycle00264 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint c3e476876002fe624095bd95bca612a648c6e0d90fdd47a76d159e9f463134f5.
def localCycle00265 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, -1, -2, 0, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, true, true, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 4, .triangle 23 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c6c4da7dbb19e254736e537b1ff23b87d2dcdd26426c8f9913d06cdd076c1d9d.
def localCycle00266 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c8c5ac522cc6b293e4637c2a865796ffa0454b05ad0fdb1667529cd091269d80.
def localCycle00267 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c8ed3426ae54ba2a072581917b70d75edb48dfe6eb89c47892a4238aff3799b0.
def localCycle00268 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3]
    constant := ![-1, -3, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0]

-- Cycle fingerprint c90653f0e2c102c55b8e8e58b0fe65506aafbd42e683f3c98ac2f07e64623e1a.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint c9183f2bdb6ce6c9c7fb5d226cd84a7be886a70df2d43a4f000330fb901772fc.
def localCycle00270 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 2, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint cbbedb672fab911a146caf7c7646ef2a473d65a3c170c486f1dea28d2164e60f.
def localCycle00271 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint cbcc267d8085d35bc6a9350d6c54165b892e70705ff1953779dc73bd9e0abde0.
def localCycle00272 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint cbd61a83d8a3c28ee678c26184ec276137961ed1119ace957ff9b5c2be48fe30.
def localCycle00273 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint cc6f171c3f0c182fab1939b43a5b350effaee656d3e1b6fa4baa5744a27a818d.
def localCycle00274 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -1, -1, 0, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint cc957ff5ca978de30c37d63cdeac2f59e1b16c570ca817bd464aa580813979ba.
def localCycle00275 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 18 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint cd1f596d5fa68630a3279befa49e82a82b9ebd755602041050289e9f5ad1d9d4.
def localCycle00276 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, -1, 4, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .gapLower 3 6, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint cd4bb8a8ddf15d55a79da3c6208ae0018c58dad93ef9ffbce07358b1e3813920.
def localCycle00277 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 4, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint cd6c5d3ac58b6fd4fe593b1cb0beb7ce3d30e8e062b6e2217d1653e5c2f8c9dd.
def localCycle00278 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint cf0c50956cb9d49207bc3811a017c2cd98831a79d4b0ae9dae60cd545bce3454.
def localCycle00279 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, 0, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 19 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint cf71fc83d16f0439132916bd1528bc8e704045644e4ed1424845db6dca6f68ac.
def localCycle00280 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint cf9f3bde436e073ed2490f423fbb3a3528b088f0777296eedca842545d8c0e12.
def localCycle00281 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint d01789eaea60c390b39f55a5dacbf1e8e0c168649e87ee01516505d214b84a7f.
def localCycle00282 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint d02574c20ff26f52de69ac9dc7cff18ffc5abe9b42241bdefeb2d4ca433ef85b.
def localCycle00283 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint d329bfdb5f0afd0679c6b3bdb6108eb9b8f499d97584ca6fc866e53696209651.
def localCycle00284 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d36b37573179409942ab81e60934db22962a7763f428c1e1697158655c8f5587.
def localCycle00285 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint d3ed5ca063015f3f461ab505b7e961982f77530138ace7d36b668b20e0dd97c8.
def localCycle00286 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint d490265b31b548d899965d00752e2a7c9a77b6c138ffc945224e7a507899598b.
def localCycle00287 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint d4bd78a532e0bbd80b284853492b9894c0f3ce58c218034cb7a0764efa2cc38b.
def localCycle00288 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint d5c563cca8ac08f0574a16611f0d727cac5810fe398bc07046a52ba1a80bc379.
def localCycle00289 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, -2, -1, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0]

-- Cycle fingerprint d78ebf0c3d756ae668705cb7b3a65ddaf75790fb37fe8fd7d4a49d93bb440ed8.
def localCycle00290 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .triangle 4 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d79ea759a15c5e3e99af63ad19a77cf22ab7cd7bd4535449c7fc7e1740ff5584.
def localCycle00291 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint d86ac741839982b87f14681df6bfe89844047e15803a6cf71c2453c5791f6c25.
def localCycle00292 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -3, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint d8daf0f9d64edc7462bde4af476270c89dcf75e69a48ecb2ac40272cab1306e5.
def localCycle00293 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 16 2, .triangle 19 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint db0c772765c21a8865d52e4b92b91065d47e32c815e98ae6706fc5e73e759401.
def localCycle00294 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, -1, -1, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint db1ef75b43b5bb1411e703a3d2bdcb931001bb47eac73167a5808f5604b89bcc.
def localCycle00295 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .gapLower 0 4, .triangle 11 0]

-- Cycle fingerprint db6617533485c89579f91a406d4a4998ea33796455736de2840a10e2dd7de6a8.
def localCycle00296 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -2, -1, 4, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1]

-- Cycle fingerprint dbdf77c43e00f16d3fc5fd1265e9b351bfaed8aa850913cc35266ed6d8f0a88a.
def localCycle00297 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint dbf3c802ebe988581656f8c4241ed9c094aefcb6f84a2fe11dc6e695732c03df.
def localCycle00298 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint dd2b4b292c353fc86e48ce486b5eff9e41519bc110ceb9d1de5a1df28806ac4f.
def localCycle00299 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 1, .gapLower 1 1, .triangle 15 1]

-- Cycle fingerprint dd867d369a4ca4fbbb3f88d66ee4ee7b7e5013fb92890c96e57cc0ab44c2a101.
def localCycle00300 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .triangle 3 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint dd9ab328d6c7c3e91e869d152c9986d485a39ba9997b04bd42eabaa6c8cb40d6.
def localCycle00301 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 21 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ddf4ba65eea08fcee9d8203f49a647cad88fc9fa8982b43b7fb593dc6b2c0f18.
def localCycle00302 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -3, -1]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint de8e11cf24d805c34f6060d13d5ba62fd5e696bc6828f558830075216702d6c6.
def localCycle00303 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint deb6e6a641455322efdb01619d8496298afbafdd0723bed2f0b69508e62b2986.
def localCycle00304 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e03a79113d1aee6ec2a1f630dd0b0eb59a6d3eeb687008cdef4926a9186e4e1d.
def localCycle00305 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .triangle 16 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e36e4110d2f5b3fd1290b1713e419533ec1adfdfa0f96592716664b55f64c0e8.
def localCycle00306 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint e37becdb971389c5c99e3a49e37340bed8863908c15fdca534d87f1a576f3928.
def localCycle00307 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e4c74d782d3e5459de0bb1e936570c7cec7e3485628743d445014980e428ffd9.
def localCycle00308 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 16 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint e565f037e8e80421d48be1c0566e310055d3622d18c1704a6081d0c7aa495853.
def localCycle00309 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint e6e73ceaf371ff969c5ccd353b79dda65af0e8a7d90200f9af40e5caed096e70.
def localCycle00310 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 0 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint e80cbc7bc8f34a97def172326717796924011d90881d75b2123bcd9c772abe48.
def localCycle00311 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint ea22979939b76075df732820c9e18837edddef32a9e3fb48d69c7b470b5347cf.
def localCycle00312 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint eb65f6cf098fd0aba362ccb5ac0758fa58458c1ba84850a11f797627f1cad897.
def localCycle00313 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint ed23ec2ac0f96313206b798d7db0a8c099600e75720f994a8f9229b83ce58b60.
def localCycle00314 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4]
    constant := ![-1, 0, 0, 3, 0, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint ed340085c6c1399060f1d6f030cb7483e64b8a680193ad73268b82e9a9633aaa.
def localCycle00315 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -1, 0, 0, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 9 0]

-- Cycle fingerprint eed6e811d365650164c8c4b7ef15bbaaa99afc46d08a99db4f26deadc0cec1b1.
def localCycle00316 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint f0004f9a8779bedc5422c3804fc45415523cfac16b27790212bec1748ff5f32c.
def localCycle00317 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint f1eedef503ed3c9e6bf23f3d237ffb4e55c38a613ca3454c7202af60beae0bbd.
def localCycle00318 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 18 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint f244273bf4f1f0eee457232617e2b3b9e0f536e7290f4cec493102c7e673c0e6.
def localCycle00319 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, -1, 4, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .gapLower 3 6, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint f36c4977cbd1a1fd49924a9175b2d6825ba8ac02aa726b1447ddbda8f705d185.
def localCycle00320 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 2, .gapLower 1 1, .gapUpper 3 2]

-- Cycle fingerprint f37e010b68c2dfa712ef5477ebedd8514483a189394cef50dfaf9cbb0686e93e.
def localCycle00321 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f3f1563bc24b5bda193eb4de6e3a0e7c1f8a8ab0f8c47c774d809e66db02d6d6.
def localCycle00322 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -2, -1, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 19 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 5 2]

-- Cycle fingerprint f4dc094e6650c9366f76c19e0e5bc03c6516f324e1c5314dffade2ad5cdc0f8e.
def localCycle00323 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 2 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint f57461ab9f1c2151295bd07e37ab78b9ef388df90ad7cfd4fb4634ed6785196b.
def localCycle00324 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint f7562796ec15749a7a4b851446f8d670789baa7b8f513fc7f59cbf10a7d06d12.
def localCycle00325 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint f7960169e75a4c4c419338fb9232af2858ee4c3efe638037b53a2c7626d3e061.
def localCycle00326 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.triangle 3 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2]

-- Cycle fingerprint f7d08339d3e37755a9838fcd268d78bdf6714d1e615bcd8efe262bf930077275.
def localCycle00327 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint f81bb03dc592a7c180522acf93e417ec05aa4bf419f6539d22a37770cb0c5d2d.
def localCycle00328 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint f82d3cb9287cbb13d95d8f5d48c273c7d5c0e9f266740f9fc0b625bced52173d.
def localCycle00329 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint f8867181eb4226b8deabeefbe52136cdcee4df7ed70e19e995625b5fdd83bfb4.
def localCycle00330 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, -1, 0, 0, -2, -1, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2]

-- Cycle fingerprint f8924e79e6a1a106c2420ce729b85dab705d54fb32d14d740ddd918572f67b92.
def localCycle00331 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6]
    constant := ![-1, 0, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0]

-- Cycle fingerprint f89da3aea8acea50e0d834ebe72cea4699efad55a35b42610fefd8e02ad0a46c.
def localCycle00332 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 0 3]
    constant := ![-1, -1, -1, 4, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 5 2]

-- Cycle fingerprint f8c130adfef5ee145ee1b9bfc6c89949347bf5154efe0b04fed86e8625680534.
def localCycle00333 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4]
    constant := ![-1, 4, 0, 0, -3, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .gapLower 3 6, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 21 1, .triangle 19 0]

-- Cycle fingerprint f8f41bd1fb4e461a5aeaf83d58c37c142aaec1eac303ab767b19be171941f205.
def localCycle00334 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint fa06ddd8e65ead5c6f51745319f8bb735d90bffd27d9e453eccde5d0c7bf4b8e.
def localCycle00335 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 0 4, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint fb3d8a883566edb5dca2a4b65d0a8fdde5a663bf51a75230de3c3c1060dac68c.
def localCycle00336 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint fbd894196ce0fe6e055947c0c6c31d4317b826288ca7a307f0605e2f8e3d0d54.
def localCycle00337 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3]
    constant := ![0, 0, -2, -1, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .gapLower 0 3, .triangle 5 0]

-- Cycle fingerprint fc24085f08adcae31befb944faac0c2f0edda9f13d2371c9a75683f3c940ea62.
def localCycle00338 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fd08830f72978010451fd7675dbe89acb7dbb0d10ba87c7bef2a30a64b8eb894.
def localCycle00339 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ff4bcd75ccfd7c1e65285ac011567d67f03e15719b270460222752ea2080671d.
def localCycle00340 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint ff537a9dad40ebe8645efa85f3a04db544c36b00ca53aad4eb343d677d2f1b02.
def localCycle00341 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .triangle 2 0, .gapLower 1 2, .gapLower 3 0]

def library : Library := fun id => if id < 171 then (if id < 85 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 74 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))))) else (if id < 79 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))))))) else (if id < 128 then (if id < 106 then (if id < 95 then (if id < 90 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 100 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))) else (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))))) else (if id < 117 then (if id < 111 then (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))))) else (if id < 122 then (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))))))) else (if id < 149 then (if id < 138 then (if id < 133 then (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))) else (if id < 143 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 146 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))))) else (if id < 160 then (if id < 154 then (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)))) else (if id < 157 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))))) else (if id < 165 then (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))))))) else (if id < 256 then (if id < 213 then (if id < 192 then (if id < 181 then (if id < 176 then (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))))) else (if id < 186 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none)))) else (if id < 189 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)))))) else (if id < 202 then (if id < 197 then (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)))) else (if id < 199 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none)) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))))) else (if id < 207 then (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)))) else (if id < 210 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))))))) else (if id < 234 then (if id < 223 then (if id < 218 then (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)))) else (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none))))) else (if id < 228 then (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)))) else (if id < 231 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)))))) else (if id < 245 then (if id < 239 then (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)))) else (if id < 242 then (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none))))) else (if id < 250 then (if id < 247 then (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)))) else (if id < 253 then (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none))) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))))))) else (if id < 299 then (if id < 277 then (if id < 266 then (if id < 261 then (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)))) else (if id < 263 then (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none)) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none))))) else (if id < 271 then (if id < 268 then (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none)) else (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none)))) else (if id < 274 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none))) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)))))) else (if id < 288 then (if id < 282 then (if id < 279 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)))) else (if id < 285 then (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none))) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none))))) else (if id < 293 then (if id < 290 then (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id = 289 then some localCycle00289 else none)) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)))) else (if id < 296 then (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none))) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id = 298 then some localCycle00298 else none))))))) else (if id < 320 then (if id < 309 then (if id < 304 then (if id < 301 then (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none)) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id = 303 then some localCycle00303 else none)))) else (if id < 306 then (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none)) else (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none))))) else (if id < 314 then (if id < 311 then (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none)) else (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id = 313 then some localCycle00313 else none)))) else (if id < 317 then (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id = 316 then some localCycle00316 else none))) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id = 319 then some localCycle00319 else none)))))) else (if id < 331 then (if id < 325 then (if id < 322 then (if id < 321 then (if id = 320 then some localCycle00320 else none) else (if id = 321 then some localCycle00321 else none)) else (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id = 324 then some localCycle00324 else none)))) else (if id < 328 then (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id = 327 then some localCycle00327 else none))) else (if id < 329 then (if id = 328 then some localCycle00328 else none) else (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id = 330 then some localCycle00330 else none))))) else (if id < 336 then (if id < 333 then (if id < 332 then (if id = 331 then some localCycle00331 else none) else (if id = 332 then some localCycle00332 else none)) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id = 335 then some localCycle00335 else none)))) else (if id < 339 then (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id = 338 then some localCycle00338 else none))) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id = 341 then some localCycle00341 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 313 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16384)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .low (![28, 302, 246, 87, 181, 207, 161, 120, 136, 81, 39, 231, 85, 69, 220, 11, 285, 133, 300, 11, 334, 240, 33, 311, 218, 288, 10, 189]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16385)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 0, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 53 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16386)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 53 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16387)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 166 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16388)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 22 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16389)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 197 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16390)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 316 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16391)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 165 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16392)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 3, 2]], proof := .tail 313 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16393)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 266 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16394)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 267 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16395)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 74 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16396)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 180 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16397)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 3, 2]], proof := .tail 27 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16398)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 21 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16399)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 21 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16400)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 257 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16401)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .low (![177, 302, 215, 77, 40, 281, 161, 120, 136, 290, 115, 321, 85, 84, 171, 113, 174, 133, 259, 341, 93, 240, 89, 78, 218, 169, 10, 189]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16402)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 315 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16403)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 18 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16404)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 266 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16405)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 148 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16406)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 74 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16407)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 18 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16408)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 156 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16409)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 329 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16410)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 7 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16411)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 4 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16412)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 203 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16413)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 224 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16414)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 0, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 163 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16415)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 18 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16416)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 188 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16417)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 52 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16418)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 252 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16419)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 106 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16420)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 134 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16421)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 313 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16422)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 339 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16423)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![271, 228, 284, 326, 12, 100, 86, 206, 186, 127, 127, 190, 24, 280, 304, 330, 303, 143, 168, 236, 96, 162, 60, 103, 218, 5, 222, 137]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16424)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 273 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16425)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 104 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16426)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 193 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16427)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 3, 0, 6, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 101 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16428)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![268, 270, 249, 122, 172, 319, 204, 141, 82, 208, 208, 61, 23, 149, 219, 17, 47, 337, 25, 239, 94, 159, 99, 14, 9, 276, 157, 254]) }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16429)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 194 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16430)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![102, 299, 112, 54, 55, 198, 227, 305, 209, 83, 232, 201, 16, 92, 91, 233, 325, 57, 213, 323, 183, 70, 19, 103, 218, 126, 164, 160]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16431)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 121 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16432)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 192 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16433)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 146 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16434)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 287 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16435)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 64 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16436)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 123 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16437)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 184 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16438)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 138 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16439)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 114 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16440)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![150, 135, 245, 130, 12, 292, 298, 36, 32, 34, 50, 178, 293, 45, 308, 105, 173, 41, 314, 205, 310, 153, 248, 68, 223, 217, 226, 237]) }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16441)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 255 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16442)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 107 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16443)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![262, 320, 245, 130, 172, 200, 170, 111, 32, 306, 306, 263, 88, 45, 308, 243, 279, 322, 314, 205, 310, 153, 248, 68, 223, 332, 199, 261]) }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16444)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![4, 3, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 79 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16445)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![4, 3, 2, 0, 6, 5], ![4, 3, 1, 0, 6, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 283 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16446)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![238, 80, 58, 124, 253, 317, 275, 216, 274, 152, 265, 109, 214, 15, 98, 72, 175, 327, 6, 340, 116, 318, 75, 8, 318, 282, 108, 142]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16447)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 196 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16448)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 2, 3]], proof := .tail 182 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16449)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 2, 3]], proof := .tail 182 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16450)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 2, 3]], proof := .tail 269 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16451)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 286 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16452)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 297 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16453)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 251 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16454)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 144 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16455)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 144 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16456)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![6, 1, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 258 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16457)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![238, 80, 58, 124, 253, 317, 275, 216, 274, 152, 265, 109, 214, 15, 98, 72, 175, 327, 6, 340, 116, 318, 75, 8, 318, 282, 108, 142]) }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16458)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .low (![238, 278, 58, 124, 253, 317, 275, 336, 274, 152, 51, 109, 214, 221, 98, 289, 175, 327, 6, 340, 116, 318, 75, 8, 318, 282, 108, 142]) }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16459)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 266 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16460)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 43 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16461)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 312 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16462)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 269 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16463)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 1 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16464)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 1 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16465)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 44 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16466)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![59, 129, 38, 124, 253, 167, 244, 35, 274, 272, 154, 30, 214, 46, 98, 66, 242, 327, 6, 340, 0, 31, 75, 8, 318, 282, 108, 230]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16467)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 197 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16468)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 90 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16469)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .low (![65, 2, 38, 202, 253, 151, 295, 73, 247, 155, 331, 29, 277, 128, 119, 62, 296, 117, 132, 340, 139, 31, 75, 48, 309, 282, 335, 260]) }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16470)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 74 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16471)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 71 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16472)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![1, 6, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 63 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16473)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 176 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16474)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 110 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16475)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 4, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![238, 3, 249, 95, 253, 333, 275, 294, 56, 42, 49, 256, 214, 118, 145, 210, 185, 291, 187, 328, 191, 131, 234, 241, 318, 282, 108, 195]) }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16476)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 229 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16477)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 20 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16478)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 179 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16479)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 125 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16480)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 13 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16481)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 0, 4, 6, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 97 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16482)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 97 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16483)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 97 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16484)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 250 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16485)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 67 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16486)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 158 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16487)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 301 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16488)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 0, 3, 4, 5], ![6, 1, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 158 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16489)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 26 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16490)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 26 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16491)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 44 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16492)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 212 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16493)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![1, 6, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 307 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16494)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 176 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16495)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 110 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16496)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 147 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16497)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 264 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16498)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 76 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16499)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 0, 4, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 67 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16500)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 0, 3, 4, 5], ![6, 1, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 211 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16501)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 0, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 44 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16502)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 0, 4, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 110 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16503)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 0, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 324 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16504)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 0, 4, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16505)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 0, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 53 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16506)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 225 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16507)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 2, 6, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 0, 6, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 338 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16508)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 6, 2, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 140 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16509)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 37 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16510)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 4, 0, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 235 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16511)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (16384 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 16384 ≤ id.val) (hhigh : id.val < 16512) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 16384)) = true := by
  let j : Fin 128 := ⟨id.val - 16384, by omega⟩
  have hsum : 16384 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (16384 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard128
