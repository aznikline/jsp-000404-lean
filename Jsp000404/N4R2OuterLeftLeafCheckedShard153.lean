import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard153
open N4R2OuterLeftReplay

-- Cycle fingerprint 0034bb5d542fe65a71573cec8161f510a8645f65b7122c510585caa5260803fc.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, -1, -2, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 08a3674b8d2f832a71638f668cc5486af18c9f141e5076e18385810b64214a62.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, -1, 0, -3, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 094a309351baeb03dd8486a97a963018ef5fb81d19d40368a0d10aea340b4e07.
def localCycle00002 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 0a0069b6f48faea17553917fc11d118a022f8c673e0310cf9e53fbb3f152eda8.
def localCycle00003 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 0abb1d4b0b838a476b1342fc76be6c51c7c19f38257109c078f2ace52ee42c63.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 0fee9f081a69f64ceabb88ec3a66bb8cc995365fe5ef1411bfb6269d05a2ea6e.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 113976cca12c5634e9c2564d3930a3bb8918bdeb006d86a9ef84b5542f787f80.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 183fb7a0efa3b66b3e2c4c285ae2f6e587b5f298beb04572583e46c965bb4546.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 33 2, .gapLower 3 0]

-- Cycle fingerprint 1dccd93791357810452cf98868ee3f83fc3c79059e8cc4add54c40ea97172e68.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, -1, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 1ddc6e336e247f01ab128761291579a8a38eeb4a836dd020dfbf5c9f41be8a85.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, 0, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 1f6384f8e98a72c018540d628d750bff34b95312a9572cbd08a5feafe980fbdb.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1f6948e111be30a0e465c280198705dc6cb4b265536b17c96369a5e234cc311b.
def localCycle00011 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 269dcc85a64faff53d82ae1c28f27702b1187e7f998fe0e3290aff294e9e7a0d.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 8 0, .triangle 29 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 26cd062244703a593bcae56a2e6e2c74fb536e31a19ebf69eb4a9d9a7e31efa0.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6]
    constant := ![-1, 0, -1, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0]

-- Cycle fingerprint 2b4d8ac667e2c34a6da75f0c4357fbab6db8f91bdb57a84ea6c21f06f2d1b8c9.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2c588bd75aa45b73515e05ad9762e7f830f103452dbb71fa0bd475e6ee3ef101.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 311ddc7f1a0fc61ca05376fb22022e2ef7a406b79ceeee20de84f6f7b04f9d5c.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -2, 3, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 31514dad290b90d0219a3811e6f484f0baa2b5eae32c554ce219d641478af668.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 0 6]
    constant := ![0, -1, -1, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 2, .triangle 6 0, .triangle 16 0, .gapLower 1 0, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 2]

-- Cycle fingerprint 349281970ba93dc71f64990ffb9c65c05afcfeef897bebd764d99285a754088c.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 38d16df94211f9b3b230f164b9af85c5b2b02fc83973bc2b7c5c4a6726fe94f7.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 3c1c6866f5d6954be2d368867724d77fd6c623f014c9f3c67150112ad79763bd.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 3c6dff3232f31933db65af9491aa6649965c5933a937cfd36a4fc7783ad79025.
def localCycle00021 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0]

-- Cycle fingerprint 3e8b3d6b7c555f90e01cafc3246e90e696e871bb82f38f09a18fd66b84e20278.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4139d31eb6a511c1c2ff9848a5fa07e5d47b0ec4082c373a9e18116d6a57fa3b.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 41414140b04ce34b94b12752aee8a9214438bc9a3bad00ced23b78aa6de67d28.
def localCycle00024 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 48c974551d9d456077d192d7d059d1294123de917fc7f7239acfda45b1dd319c.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 5183c878eefc19ee82e74eefc74fdf751c8fc2c4eda903747d21c144182c93bb.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint 5aff1cfa53dcff50e74bba5f8099d31249309c19a3936e6bd55239063a2e072d.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 5e9b4f7251f6b0cc1d5501878f888cdd02de48ef919d8633bf71628cc50b84a0.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 5f8834c4f68c62b411f331cedb38787cdfde354daf34c384cb9e16c5ed713b2d.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 631692c85ee29f06da10877bd9f566ff89f2c38d8ee042b4c67d0453da8c6b81.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint 63a7bcb796605a5ee88703f39a34e022c0dd34430d322b68b66789e800528101.
def localCycle00031 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint 646ecb45d44fbf2aa2a5ae84be93c0cc1e80727462fde10e310159688a5b59b6.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 21 0, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 65623ddf832e59342fdc21e4bf9bce3e01a149ea06bd024d072e35eb40672ff8.
def localCycle00033 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, 3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 65f032112646c407a93da27fc4bac30c35c87771fb06a41a4cd9c5d20bee6f0a.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 66418fa9293373ee06089a3027c038efef1d1ba6e599557b0eb1b955803e1cb9.
def localCycle00035 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 2, .gapLower 1 3, .gapUpper 5 2]

-- Cycle fingerprint 6762cf149237247c2e7c8ba00b0923cf573c933f75f31bad7a38a9df19768c86.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 691211926c43203020a8d2831eedd8113ebb59e121bb990e0474225b52a94437.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 6e1f629a0436a63bc7d4a1c753cdbed55c5cf6a1db955d0ae85a3444d8330bb8.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1]

-- Cycle fingerprint 6e224d6d1df41b63091dee4d9734307e69797a8674ea5b665961084cb78fdf98.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 70438afa9f2a3053502e20e2b837de3982f279cc180bd0d1bbcd768b467d18a0.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Cycle fingerprint 7048829949fbd861a0ce6a2d38b02fae0f27ffe8f792a7b83d408848e10e90d8.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 2, .triangle 8 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 70ec8fd5a8b826e5464190518ea8a7118d70f83f2dd8c55a2e517d3d169721e3.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 722ab56d56b5c16e9f7bf81899bfb9ac013c1059c00a8f87f249395dbc5fb798.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 7245d5f88be066eeb37fbbdf4ac826d8c729d7ea5b89c2e47501f98af60b1d63.
def localCycle00044 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 72e4d8729a37998512daeffa21866a7b0c3370b1191947c91a9a8f30c9f58fc0.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 72fbeee891becab5bff3b18b7c6a9f1d5fe651826cb65b4c04797abb1f4381ab.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint 736c960af437e07858e8a216a34d3caa11f3e36054489238fa1f18bddb642646.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 7453005a6c6a3f4d65a519304e07153859e3f9840259d9ef60330dac1d7a51d1.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7604485cf46effc9a7e59768f8cad0ee2d61a86097d8e1a59d19a21fcef94b8a.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 77dcad457b9edfaf0d334bd7f856f7f3734af6158e6780b5d53cf420d38c9a25.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Cycle fingerprint 78b57c22076a9792f22d4c1b2913d9990d6f2da34827fcc31aee5561050b5f32.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 78dc52934a5ab8d3acbefcc6befc284dbe4dd0232eeaf8cba72bfa55ed26821f.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 794059ae8ce76acfba11c0e9341696263fcde1249ef8241041882890aa3611c9.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7978411700430e2b705a11430a22e82bca2a09bae5a171c919bd363250629241.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8114909c2a3e60d42446206fa720746750d5cbb8cd8dc4759702c01da45053cc.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6]
    constant := ![-1, 0, -1, -1, 3, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1]

-- Cycle fingerprint 83eb4c82b7a257b9512f30b1fd6920064354110309370897930dc1233321713d.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 86b262c3dc490bd865ae6fda2ba186f97498d5441281e58d9dda929e16f51f1a.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 14 0, .gapLower 0 3, .triangle 5 1, .triangle 6 0, .triangle 16 0]

-- Cycle fingerprint 87973136829ec07d9865b2c7c1e626159e33962e2c36deae8841a5f4f9d78989.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 8826069bc41f788bffc10f25ee2bbac7a002fdf2028fea2fabf7d4885c64dbf8.
def localCycle00059 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 885483e52f73240b410581590addcee37ef034d900f237ed306426c3154b5720.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 89fc38981f611e7e28a792a679eb529fbdda1af274ba25c572a41ccafef30a4c.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0]

-- Cycle fingerprint 8b6a1d00670761381965e35afc93898615e42cc2d7e3589eac92626f7ce6d0fd.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 8f8aebe443411ac621591fc9afafade52d01661c1cf1f526b6e9e27aea2053b6.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 90d28ad6a787faf1a01d049f69804d9af1ee05b30f0d4d4afbb4e5c57fff1a11.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 949d236d2a08a4d38e07696cdcfb96450c137d609acc4e7499c5eb26b31190ed.
def localCycle00065 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 95a5fd9ffcfd0c3913133e8ba6f97c0264ef257fe1a77cea19efd6257113309a.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 978a8280c97f7966cafef517e11c740ffa657f470da47d955cd1db640b89aefe.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 97d86820f916b07afe544ba5ad34a6a2c6bba5d8b9df96c6ae3aceaa28a3cee2.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 9acca963d4098482833bc52c9a734e63f377fda2bcc92915d5075cf560ee7df8.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 9be3e30a46291403b35ef33dcd7f97171e6e3cae798d55d26eb6534894f2b582.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9d2eca660af4dafc9b3f972883a07d605c1b28906c0a77802462b8550beb177c.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 9dd548b03659945d8a17b52c0034f910152705c72589ce0ca6e80224e8f990fb.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 9f16c253f991cc435a52bb9490137249c0b69a50ae618af3f1eabbb29618cabd.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint a9ef6d1cf78cfa918f3b7727086296f094d64b0114bbf840dddde8dc41d8ad7c.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 3, -3, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint ac8bc585b7435997000845c75dcf3fcc39dbe8b3d3b1137362648cfccc5dfebd.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint adedc6d8fc48517d191d5d3fcb54829099a860ccc1fbd5d71388fe749718b65c.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b3a7f7cbf6f755ae9f52a074d321b8ad2dc3d90cd7b342a42a92e4e0cb05b245.
def localCycle00077 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint b452cb94691629e0ed940ac5c48cd37cbdb34d515307e79812c087f4ff63ef73.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint b4d7a1d1b07b567ad756a7de0150cbd9ea507852b48b9a5e81cd6d19d8fbfbef.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint b548fd84fb23f473baacfeebbecc4f3c08f1232798e6f74004b2072e0d996c87.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint b8d66862cc330790161061c9d02bd4b3494ba6459f3261a4257ebc71860e981f.
def localCycle00081 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint bb47bf1f13d97b4d17e4ae08342dad826ac54aa971950b44cfa632de587b77eb.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c31cceaa446a63f53e6ef2dfa4c3233fb9659328c37077eb9fc4c9582afa2d55.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint c8424785dd15c0b42138032d2ac070d65aa4618d606ede5dd08f741c4c012cdd.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c95cb2e7c13c9619fb170fb335b20d6b7504ea8dff60735ac134ef5b2da743ab.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6]

-- Cycle fingerprint c9a82104974c7120170cf13863d3f84c8f09cb41f6ff2e54399ea1290733ac85.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint ca1422d3d97f26a9766fdd1f36e745bb839ad8fe5ff47a535e29fe361ec697a9.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d3beaef309309fdfbf74ed46565b24b03571c901950d6a649c004ff13bbcaa7a.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .gapLower 3 2, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint d3c062b4b5db7bd1a914e323f9335d04a81dbe92b0903147a85b55ae01ca92ef.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint d4aa8b8639d5becbfe8d73367e290cbf0c839bbab7cb77444f6452dfbd6f4ab7.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d5f9f79206509a4dc5c11b07190a52a6b009b1f4bdf147e3ba7b71927a5e4062.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 0, -1, -1, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1]

-- Cycle fingerprint da588134e6cc0eab58f1c6dd09a5ec898470fbc20349b294a59a69ccd17a9398.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint dca8ead6353f3dca8a946fa1a5e390077b94eff9a84fab04a687783fe767ff87.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint dcfcc567d307518ba9e64136ba65b043887a3449b8d80005b4d54aff5308880e.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 3 2, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint de1f896b559eb1aa0132c6100c7eda9baba87e63357f70c8b58da5357c06fec4.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint df7085dba01fb7752f9c029d21bb49123eb2b94d6e9671ab5408b044fb81503f.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint e1a5b36c89b390bafc4aa36b6ebba2f2222ab62a1db929a69ecb8654b933dbf0.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint e5e2ca4f6324c0355b5a6d0da63c84621b265c0ec3ee6b3433275dd0c69ebf16.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 4, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint e8a8ed71334481380a4139ffddd0455eb2e6bebf065a91455a1aa3a42b64df0a.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint e9d405677c861d242da2f0c0aee89e6f6f25c42157a7223c4ba8d19573df48f9.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 4]
    constant := ![-1, -1, 2, -2, -1, 0, 0, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.triangle 16 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 21 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .triangle 8 0, .triangle 6 0]

-- Cycle fingerprint ee4eb0f74ea33b97696bf763f62c31c9217f0b8bf0c2ac4e5b5fde3888699353.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f1107435f3e5b9f942b1f95c72d8a10fc1975e25dd47f7adeb6ffcf73e5fd91d.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint f1641606c45d040100e5fab9de849e7eb1a34f67d776a645308d749780b0b8c7.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint f23d2c4f1377a9250b9d9b6437d9f895e487300163bc4997cc37c2df57195add.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 0 6]
    constant := ![0, -1, -1, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 2]

-- Cycle fingerprint f372a20b10b5f0ac3b09235c6ce13b95dbb2b4c9e8c0cab7381f81a7abfd9ab1.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint f687f9f01602ef1423dd8397e7c6520469018e1d2d6d392057fc228f67f6288b.
def localCycle00106 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fc24085f08adcae31befb944faac0c2f0edda9f13d2371c9a75683f3c940ea62.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fcc3bec42e1bb6f7f51467fcf1fc6d4b697edd15e56765b915f19db94da11147.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint fef9387f1d5bc807b4408e649acc63eec3c33baa92a618676b034f7a2b56596a.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ffd7b45055cdc61e417c0c07aea2bf6f9ca1e58a5a4fa5b66a0e3b652b8910a1.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 0]

def library : Library := fun id => if id < 55 then (if id < 27 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 20 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))) else (if id < 23 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))))) else (if id < 41 then (if id < 34 then (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 37 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))))) else (if id < 48 then (if id < 44 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)))) else (if id < 51 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))))))) else (if id < 83 then (if id < 69 then (if id < 62 then (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)))) else (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))))) else (if id < 76 then (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))) else (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))))) else (if id < 97 then (if id < 90 then (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))))) else (if id < 104 then (if id < 100 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 107 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 32 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19584)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 4, 6, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 6, 0], ![4, 3, 1, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 23 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19585)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 3, 1, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 88 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19586)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 3, 1, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 38 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19587)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 1, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 45 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19588)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 6, 5, 4, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 3, 1, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 94 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19589)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 3, 4, 6, 0], ![1, 6, 5, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 3, 1, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 82 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19590)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 3, 6, 4, 0], ![1, 6, 5, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 1, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 82 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19591)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 32 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19592)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 5, 6, 3, 4, 0], ![1, 6, 5, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 82 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19593)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 78 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19594)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 4, 0, 3], ![6, 5, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 67 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19595)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![2, 6, 5, 3, 4, 0], ![1, 6, 5, 4, 0, 3], ![6, 5, 1, 4, 0, 2], ![6, 5, 1, 3, 2, 0], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 96 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19596)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 26 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19597)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 4, 0, 3], ![6, 5, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 50 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19598)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 2, 5, 3, 4, 0], ![6, 1, 5, 4, 0, 3], ![6, 5, 1, 4, 0, 2], ![6, 5, 1, 3, 2, 0], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 37 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19599)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 4, 0, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 95 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19600)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 4, 2, 3, 6, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 4, 0, 6, 3], ![5, 1, 4, 0, 6, 2], ![5, 1, 3, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 64 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19601)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 4, 2, 6, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 4, 0, 6, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 64 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19602)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 4, 6, 2, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 4, 6, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 3, 2, 0, 4, 5]], proof := .tail 4 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19603)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 4, 6, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 6, 0], ![4, 3, 2, 1, 0, 6], ![1, 3, 2, 4, 0, 5]], proof := .tail 102 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19604)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 4, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 3, 2, 1, 0, 6], ![1, 3, 4, 2, 0, 5]], proof := .tail 88 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19605)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 3, 2, 1, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 64 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19606)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 2, 1, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 64 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19607)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 2, 6, 3, 4, 0], ![5, 1, 6, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 64 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19608)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 6, 4, 2, 3, 1], ![5, 6, 2, 3, 4, 0], ![5, 6, 1, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 51 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19609)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 4, 6, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 2, 6, 0], ![4, 3, 2, 1, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 47 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19610)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 4, 0, 3], ![5, 1, 4, 6, 0, 2], ![5, 1, 3, 6, 2, 0], ![4, 3, 2, 1, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 88 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19611)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 1, 6, 3, 2, 0], ![4, 3, 2, 1, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 64 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19612)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 6, 4, 0, 3], ![5, 1, 6, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 2, 1, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 64 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19613)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 2, 6, 3, 4, 0], ![5, 1, 6, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 64 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19614)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![5, 6, 2, 3, 4, 0], ![5, 6, 1, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 51 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19615)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 3, 4, 0], ![5, 6, 1, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 110 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19616)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 3, 4, 0], ![6, 5, 1, 4, 0, 3], ![5, 6, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 46 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19617)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 3, 4, 0], ![6, 5, 1, 4, 0, 3], ![6, 5, 1, 4, 0, 2], ![5, 6, 1, 3, 2, 0], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 7 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19618)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 4, 2, 3, 1], ![6, 5, 2, 3, 4, 0], ![6, 5, 1, 4, 0, 3], ![6, 5, 1, 4, 0, 2], ![6, 5, 1, 3, 2, 0], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 86 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19619)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 2, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19620)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 2, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 71 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19621)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 22 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19622)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 14 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19623)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 14 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19624)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 14 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19625)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 84 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19626)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 6 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19627)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 6 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19628)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 107 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19629)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 0, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 107 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19630)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 0, 6, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 33 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19631)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 98 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19632)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 89 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19633)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 83 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19634)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 6, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 10 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19635)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 2, 0, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 101 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19636)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 10 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19637)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 6, 4, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 101 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19638)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 10 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19639)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 6, 4, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 6, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 101 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19640)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 42 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19641)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 0, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 21 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19642)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 56 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19643)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 0, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 2, 0, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 43 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19644)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 2, 0, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19645)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 2, 0, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 76 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19646)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 2, 0, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 66 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19647)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 2, 0, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 106 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19648)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 2, 0, 6, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 109 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19649)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 2, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 57 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19650)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 13 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19651)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 2, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 53 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19652)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 5 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19653)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 5 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19654)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 2, 6, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 0, 6, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 41 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19655)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 2, 0, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 5 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19656)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 5 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19657)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![4, 6, 2, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 12 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19658)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 2, 6, 0, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 19 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19659)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 6, 2, 0, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 15 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19660)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 2, 6, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 19 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19661)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 6, 4, 0, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 6, 2, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 15 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19662)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 2, 6, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 27 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19663)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 6, 4, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 6, 2, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 15 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19664)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 6, 1, 2, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 90 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19665)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 0, 5, 3], ![6, 4, 1, 0, 5, 2], ![6, 3, 1, 2, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 99 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19666)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 0, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 6, 1, 2, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 79 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19667)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 4, 2, 3, 5, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 0, 5, 3], ![6, 4, 1, 0, 5, 2], ![6, 3, 1, 2, 0, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 37 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19668)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 2, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 70 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19669)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 2, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 48 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19670)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 2, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 29 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19671)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 2, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 29 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19672)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 2, 0, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 105 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19673)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 2, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 49 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19674)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 2, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 76 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19675)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 2, 0, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .tail 108 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19676)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 2, 0, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 36 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19677)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 2, 0, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 80 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19678)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 0, 6, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 60 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19679)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 0, 6, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 73 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19680)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 2, 0, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 62 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19681)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 2, 0, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 91 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19682)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 69 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19683)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 6, 2, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 2, 0, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 73 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19684)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 2, 6, 0, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 72 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19685)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 2, 6, 0, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 55 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19686)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 2, 6, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 19 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19687)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 2, 6, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 11 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19688)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 0, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 6, 2, 0, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 4, 2, 0]], proof := .tail 97 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19689)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 2, 0, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 15 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19690)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 6, 4, 0, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 15 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19691)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 6, 4, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 6, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 15 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19692)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 1, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 90 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19693)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 0, 5, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 1, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 40 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19694)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 0, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 1, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 79 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19695)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 4, 2, 5, 3, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 0, 5, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 1, 2, 0, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 37 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19696)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 2, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 70 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19697)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 48 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19698)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 2, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 87 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19699)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 58 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19700)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 2, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 52 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19701)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 2, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 49 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19702)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 5, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 76 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19703)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .tail 25 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19704)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 0, 6, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 2 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19705)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 0, 5, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 2, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 49 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19706)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 0, 5, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![3, 1, 0, 2, 5, 4]], proof := .tail 58 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19707)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 2, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 0, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 6, 2, 4], ![3, 1, 0, 5, 2, 4]], proof := .tail 28 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19708)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 0, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 2, 0, 6, 5], ![3, 1, 6, 0, 2, 4], ![3, 1, 5, 0, 2, 4]], proof := .low (![61, 1, 93, 35, 59, 74, 104, 8, 75, 63, 68, 16, 17, 0, 92, 34, 39, 18, 85, 3, 9, 20, 77, 31, 30, 24, 81, 100]) }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19709)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 4, 0, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 2, 0, 6, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 1, 0, 2, 4]], proof := .tail 65 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19710)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 2, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 4, 0, 6, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 1, 2, 0, 6, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 103 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 19711)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (19584 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 19584 ≤ id.val) (hhigh : id.val < 19712) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 19584)) = true := by
  let j : Fin 128 := ⟨id.val - 19584, by omega⟩
  have hsum : 19584 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (19584 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard153
