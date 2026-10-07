import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard181
open N4R2OuterLeftReplay

-- Cycle fingerprint 017ab67f65067aac5a1c4cf91b4247558c19326b77267d64d44f973bb5818fdc.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 065c005d20c4105fb956b32ef38cd96151f6090598a9dadef4555d0582163603.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 06d3a5d199ee89334b1df426f1eca7173fd0f8419fd7a4bfb6db3bca19dc37b7.
def localCycle00002 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, 0, -1, 0, -1, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0]

-- Cycle fingerprint 0871209710e3cd90556680d4421a15d62a8e1dd47bb5ae9ae338e18c2ddbd0a7.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint 0c29cbbc78c40593f13945396ee272bbe51980e06c73865854851276f7c80c33.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0e5c59e5c6a017ec83fa2e4567a19a93dd1a82f0c0c125ccfc8f37ded4228220.
def localCycle00005 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 105b9ef08f3e838d85e10d8f224d6e216a6df3d5cd83a820bc62826eb5e8339a.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .gapLower 2 3, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 10c317c53b07b6f3ba21f7bf771bd07c32fa23268302e91a8607b6ad9a60b4c8.
def localCycle00007 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5]
    constant := ![-1, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 14fa8f2ae6d7a1348c2dd6d450f04924f21b010b7f7cd5678ded17fe790ff9bd.
def localCycle00008 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4]
    constant := ![-1, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 29 0, .triangle 32 2, .gapUpper 3 2, .gapLower 1 3, .triangle 16 0]

-- Cycle fingerprint 15b4ae22bfb6eda74eaf3e68513bf1c1568b4b75b13a87ad2ba9fdc13a10c657.
def localCycle00009 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 1716c1c981ebb9def2c1df4b8c04ac5638aeca1d2daf88e87b07783d374f1c42.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 185027997e38461fabc24752a0fab9e2b1a0417cff9d41548669e8197ee08f52.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 1a690bff3337032bae6ffee85de34d0d111c2d3aeefaf152fc7d054ec4bf42cc.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3]

-- Cycle fingerprint 1b1cf84b71d93faf8ffbd8e8a823eb71255c4f6ccad61ee46e6da1dfc189d3a8.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 1e32548f5bafead2c5ceae349ac24de23702af45844ea48849bced08fef1536a.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3]

-- Cycle fingerprint 1fe9fd0a12f0727ecd60ba306b7403a3c9e19f0e713a0e4880a444902635ed9e.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5]
    constant := ![-1, 0, -1, -1, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 20 0, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0]

-- Cycle fingerprint 2062179ee96c27951787c6d69e3351569ea30288c6db3a0e8f90e295fa967c95.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 25a2e0b877b9a2444c0d793fa8df969de4937bd1a8b301f6a91323bf1e4d0530.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0]

-- Cycle fingerprint 30b37d397c148dc0faab82a5802e047928850f3c5802d05693327172ff445216.
def localCycle00018 : Cycle where
  length := 14
  data := {
    node := ![.distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3]
    constant := ![-1, 0, 3, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0]

-- Cycle fingerprint 3e2964fa561129681cfc14c843cdc8dcfa146bc3fa8bbf4e2e804962c8c74dda.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 16 0, .triangle 15 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 3eccebcd270409002c59b4421aa2e57ef1d2615f57b752282a619f5730d7a45b.
def localCycle00020 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 413b6fd278418d27499885230550f8790ee100ea3febed88026bdaf682b29f9f.
def localCycle00021 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3]

-- Cycle fingerprint 420b7aea0aa96d0109d7f7b6091c0b07445158a5a69183a12cc2dfb5ebde38d4.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, 0, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .gapLower 1 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .corridorUpper 0 1]

-- Cycle fingerprint 46c10c44ee462326df568591d825ec1368f912c5d225b04c2fdbe4591bab5a23.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 49d871546a39d161a283e994b25ab2037b0f143d5027e0a3410b07e48323421a.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 4e2803d09c565e3ff52dc41fdaa9c42c7a21667b4c3cfdd0b9e526c679e242f3.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4ea2e5d787e8f2a5d3288079de3e0e6a54842644dc8369904ea5d672ca6c52fe.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 4f0373d2b03d49ead0182153158bdc6f7598cd47afcfef4eb9f1854d24323df2.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4f804474fc5e3b2e7dd0e8366c5996dcdc36700289c661d8d2c251f634030199.
def localCycle00028 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 4fb1daf3e57eed5e9e162c2449d4830116558f245fe0ee765715b7502ba0061e.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 51b2d8c2916e477633358cc0ab9de187c1836b14607637361b471321a9c6d385.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint 520b49837d921443c4b359639ed0ca81d00a898ad67f569876369f6f2eb34a02.
def localCycle00031 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Cycle fingerprint 5382308f4c8c3549ff8242e066cf0ee70404c1ef7e4740190e8ad3fb91ba0316.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5c2c060a6f3fae653601f3e9899a59fa12a15651206e95fe2bcd3b9715bca9e7.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 62349eded64c11f2e1d5e52851a17d2ef5e954d3513aa497f53d790c3119b492.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 6727bda8f2952c95791d0aacf3adecbcda1596cd5bcf7e3cf2c8e8e424881c5b.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 692de0017a86a81fec80645d93c3d377d61e811b7b81d34ca6d738489104b9d7.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 6ba0fec324090aec4fb093d29e9a0f68ffa7b71983f658b00c50eb9d20cba3d6.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 6f7f706279ca1132dc7ff64202a3df0e4633a92d70f9b4120e60cdd30475dba9.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .gapLower 1 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 6ff88c93a5ec77d0228f0b1a7dbfb49ba582503000b490bbf03456cd5b1416b0.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, 0, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 26 0, .triangle 20 0, .triangle 21 2, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .corridorUpper 0 2, .triangle 5 0]

-- Cycle fingerprint 705d93a5ba7528bbce2039631228a6d9221c5d3a5d16f429fb45e608035eca38.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 7175a4e8a7af655db9d6da98d4a8ec92fcd9c433cec8d49f682ff6a33bc17479.
def localCycle00041 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 71a0d0e1a6cb1093973bb1c0e7486a3be7f0aae6fa1d9dead2676ac178792f0a.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6]
    constant := ![-1, 0, -1, 0, 3, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 23 0]

-- Cycle fingerprint 7861c6eb1596e25d2d0709f2998e7dff85b518eeadca87335cd2482c67dffd1e.
def localCycle00043 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 1 4]
    constant := ![0, -1, -1, 0, 3, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 23 0]

-- Cycle fingerprint 7e55d637b0ea3e86c1af7494f0b304be5ed8f7dea57f37588faef06aa5c4142d.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8056d7c5508cfb9e7a4d1f44bec289a8289f3439beb51bb07b1d48b4d16656af.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6]
    constant := ![0, -1, -1, -1, 3, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 34 1, .triangle 30 0, .triangle 17 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0]

-- Cycle fingerprint 842e32502e819473cc01a76b9449d50b92466f66b4f9f050eb0959f1f868d1d0.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint 8b2dfbb9727a020344722c5ccff6c04424d200854a808ce2350a96624aa2e763.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0]

-- Cycle fingerprint 8c881d0a16404522eb8dfeceb8d4005f9b019b9518bce754e45481e0f032a6e4.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8cde08edcd823de99b878e3b70d5480bd4c6536c3aefea8579f336227e95b6f6.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8dbf6eb256500ad86bc8d08f056590bbaa5d4464288d033eb28d61de6bc850ea.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 29 2, .corridorLower 2 6]

-- Cycle fingerprint 8fb3aad5e06c9daf3a63c065824114577b842f42fb24997948d99e82db236f79.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint 906e5751e7c569be4f8c48858d4af6f4739512cc52ab57202fbdfa1878d5c56f.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0, .thetaNext 2]

-- Cycle fingerprint 916885d062d1c8cf3dfb8a1dbdc380e496c50f2b9fc78ea8a2d7012ff99f719d.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, -1, 0, 0, 3, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint 9432e86e8cb707ce1b8b481dae2e25ecc0fa70422b407ebadd04625e7cef66a2.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 24 0]

-- Cycle fingerprint 94463162f46496733b0554324f8680295936a1084014a8e8f29eb9979c155c63.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3]

-- Cycle fingerprint 959f6612fcf7d31535ad1525b7a0a48b8e0b0b41d5f25f7b0adf6b0e5f8b3664.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 96cba37712fd649450cbcc20e0915694febd72ed477698335e2cbcb8d8b6bd52.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 982c4e4e1d04c8aafc710989a975222bdf431770c6511748be49f62273481cb9.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 99106381720fe0e53f6c71e68f3aaa7af2b99ca4f727e54d5a65275cd5aa4e83.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5]
    constant := ![-1, 0, 0, -1, -1, -1, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 16 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 26 0]

-- Cycle fingerprint 9a7be1be347e0d9129ccd703105e33fb909534dd7e159da0c77c84eeeb8017a5.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 9ab94754552907fa89250eba0e2654cc633bf9b92bbbf81c7bb659b0cbe540d1.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint a5d1dabc66bac29117577a0934d64f500a9c0b678893c2c7fd44b63e25d7d2e7.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3, .triangle 18 0, .triangle 29 1, .corridorLower 2 4, .corridorUpper 0 2]

-- Cycle fingerprint a98ed6ad8b513b6ed1480027cb3f93005c790b1e8ad1433c7c817fa88cb7b813.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 15 1, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint ab6af540454960bd5539df60e82b7b754f462a6ddf5369ead959ea6ccefe95c6.
def localCycle00064 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ad35954cf8a5cbfef6311d35cbb58f31e0fa50e56f8b6b4decbf018e228c1d4e.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 0]

-- Cycle fingerprint adbc87928d07dcb206d9cc682226e3b73002b23599695efc12634e65bc269e30.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint afdc859792b6af2930dea22680e312d5cd32f15a71ecae3e1c2229ec95984b24.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b0851c920ed5390f87c1c2a4e8b594768cefd5d1b8a407a48b279bd6962fa5ef.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint b3beb3d40244d86fbc42adbf8a49958e2b52f3c722b60620edd17921850131c9.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint b5299ec15ac8ea26e4584c572ccd56524db3e034dade0477a73222d5305a2a0a.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint b69cd3e1e2bc67869558dc703f09a9061054fd461752bc1aaca06e81a2b5a892.
def localCycle00071 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint b9b96e6b1be2bb77b48f899ed7687f0ba9915331198c4db29a4a949ac5f2aa45.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 3, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint bcab5a7c21ab97af43bd7e42f9472957b538bfe1642bdf57105bf6971905e0fb.
def localCycle00073 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint bcb7547618a9e9a9e7e884994341fe04d04bff58ae99acc4c1cf734770bcfbb8.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint be94e11c1744350d5d54f72820a67e174dd583b4552e11d7ad94fa9f2afe9df7.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c09d5252ead648b419216ffd1f77df03d63e5aff9599a175920a3c47e5dce9e0.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c250bf38f6c384b64bcbff171eda603d96fb7fd0f68ad9f5267dfa4c5d45cf2c.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint c4a2b7db20302f15525487ef1132c3eb5647eac6eb91f05ff58f7b3fa4623a53.
def localCycle00078 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint c7b63cec5e2b9bde95d8d34286a88138748f245cb0d9c620b1548ed25fa5cee6.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Cycle fingerprint c7f682a0c7011429703e1ff61a47386f7d403bcf53ddcafc585d5689f474a70b.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint c9fc61b3843aff82ba618df109265ae7d0856db1aa999db7a898f95a9261a871.
def localCycle00081 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 5, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3]

-- Cycle fingerprint ccd788c75f9770cd605ea67b2d965681db98aab6407bfee90ccfec411397368a.
def localCycle00082 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint cd32998d535c8b28dbe258b02712c2b497e3c5686759ebbaba67ba362a1304e0.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d19800db2a779e59fc90af6f228f4777230fa098536ccffdb536bdb48538f412.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint d393b5a71bf3b7ae23b0504940e78174ff7690295734373f2d0ea84f32246d0d.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d42cd860e8a0e4226b281e3a618a5834dd0a38fe30c29538fd77583a8db1ff91.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint d4ca63630719e7c8304c354c1c37b6a80afb4f7e98fbdc72c14202b2b1435726.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint d6e30387bb2d32dbfc989ca74b9daae8c02809541610e89b3bc776f3228fcb5e.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 2, .triangle 22 1, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d7088a06cadd56ad64886f899080791d4f37f892475c2b279167f20c882b13ed.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Cycle fingerprint e3808405d75e8c0a0323459758ad43f5a028bd3a0061975fe8aba77403ee7217.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e455628218d3288087da605b7d2843e9f84fde4e7b767c4ec36f5aa0740a19d7.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint e87698c8d1afd50ad6e053c7de908e2c2bfd0fba83837ea18bb6eee061dbed89.
def localCycle00092 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint ebbc10c1824540c4f4f7bcedf2311083531abd850ae431ffc25aa879bc276307.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ebfc0aba8e86f88726cce3383fd7556bbdea09660beed695ba4fbc25bffe4edb.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint ecde36f9ede29859ac5f83d556d9742251e994e37cf2fb48993b3120e9e7ca33.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ee7b966659e042a5c91d5a7635b7be45d20e01260b71b4660c1509e78a57df38.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ee7f1553e8d7f51843f9052ed984cfe79b5a4e48f0f6980e08a8309b6151bfc1.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f2cc03df27e88b2d4d8ed043c4d4cf6ec222be3c62f226763df8970026acaa6e.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f90d4e74710ff2a3adde9b4c9791f6d73eb30617831d3ff63ab9eca26477944c.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5]
    constant := ![-1, 0, -1, 0, -1, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0]

-- Cycle fingerprint fba6eb9c720d5ea07cf7b29e8138fbc559f5378fe80599b3d5def9ef6b13783f.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint fcb2a176b1a208ae84a5e4ed41802c923975e2a1b998c069f7474d2e92ab6cfa.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

def library : Library := fun id => if id < 51 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 38 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))) else (if id < 44 then (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))))) else (if id < 76 then (if id < 63 then (if id < 57 then (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))))) else (if id < 69 then (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))))) else (if id < 89 then (if id < 82 then (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))) else (if id < 85 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))) else (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))))) else (if id < 95 then (if id < 92 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 18 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23168)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 27 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23169)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 24 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23170)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 43 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23171)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 94 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23172)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 1, 6, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 87 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23173)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 6, 1, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 97 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23174)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 5, 0], ![6, 2, 1, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 19 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23175)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 1, 2, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 61 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23176)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 6, 5, 0], ![3, 1, 2, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 17 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23177)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 1, 2, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 72 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23178)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 1, 2, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 5 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23179)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 1, 2, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 64 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23180)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 1, 2, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 29 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23181)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 1, 2, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 41 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23182)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 1, 6, 2, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 5 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23183)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 1, 6, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 29 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23184)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 6, 4, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 1, 6, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 6 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23185)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 6, 1, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 32 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23186)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 3, 5, 0], ![6, 4, 1, 2, 5, 0], ![6, 3, 1, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 31 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23187)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 6, 1, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 76 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23188)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 3, 5, 0], ![6, 4, 1, 2, 5, 0], ![6, 3, 1, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 91 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23189)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 1, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 60 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23190)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 1, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 61 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23191)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 1, 2, 6, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 33 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23192)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 1, 2, 6, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 47 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23193)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 1, 2, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 25 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23194)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 1, 2, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 80 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23195)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 1, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 4, 2, 0]], proof := .tail 101 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23196)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 1, 6, 2, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 47 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23197)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 1, 6, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 98 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23198)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 6, 4, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 1, 6, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 58 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23199)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 6, 1, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 14 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23200)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 5, 3, 0], ![6, 4, 1, 5, 2, 0], ![6, 3, 1, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 90 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23201)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 6, 1, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23202)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 5, 3, 0], ![6, 4, 1, 5, 2, 0], ![6, 3, 1, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 90 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23203)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 13 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23204)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 96 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23205)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 6, 5, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 1, 2, 6, 0, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 95 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23206)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![3, 1, 2, 5, 4, 0]], proof := .tail 83 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23207)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 5, 6, 3, 0], ![1, 4, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 6, 0, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 2, 4, 0]], proof := .tail 37 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23208)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 2, 6, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 2, 4, 0]], proof := .tail 44 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23209)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 1, 2, 6, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 9 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23210)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 6, 4, 5, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 1, 6, 2, 0, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 4, 2, 0]], proof := .tail 36 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23211)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 5, 6, 3, 0], ![1, 6, 4, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 6, 2, 0, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 4, 2, 0]], proof := .tail 75 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23212)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 5, 3, 0], ![1, 6, 4, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 1, 6, 2, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 4, 2, 0]], proof := .tail 75 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23213)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 4, 6, 5, 3, 0], ![1, 6, 4, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 1, 6, 2, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 75 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23214)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 4, 1, 2, 0]], proof := .tail 88 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23215)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 6, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 88 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23216)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 3, 0], ![6, 4, 5, 1, 2, 0], ![6, 3, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 69 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23217)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 4, 5, 3, 0], ![6, 1, 4, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23218)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 4, 5, 3, 0], ![6, 1, 4, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 6, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 67 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23219)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 4, 5, 3, 0], ![6, 1, 4, 5, 3, 0], ![6, 4, 5, 1, 2, 0], ![6, 3, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 20 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23220)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 35 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23221)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 30 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23222)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 11 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23223)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 55 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23224)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 21 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23225)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 6, 4, 5, 0], ![2, 1, 6, 3, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 45 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23226)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 4, 5, 0], ![2, 1, 6, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 28 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23227)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 4, 5, 0], ![2, 1, 6, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 78 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23228)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 4, 5, 0], ![2, 1, 6, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 10 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23229)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 4, 5, 0], ![2, 6, 1, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 42 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23230)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 1, 6, 4, 5, 0], ![6, 2, 1, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 86 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23231)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 6, 1, 4, 5, 0], ![2, 6, 1, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 97 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23232)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 3, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 6, 1, 4, 5, 0], ![6, 2, 1, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 97 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23233)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 3, 4, 2, 5, 0], ![6, 3, 4, 1, 5, 0], ![6, 2, 1, 4, 5, 0], ![6, 2, 1, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 57 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23234)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 2, 1, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 92 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23235)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 23 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23236)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 51 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23237)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 2, 1, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 2 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23238)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 51 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23239)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 26 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23240)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 46 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23241)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 89 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23242)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 2, 6, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 3 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23243)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 6, 2, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 8 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23244)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 3, 5, 0], ![6, 4, 1, 2, 5, 0], ![6, 3, 2, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 40 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23245)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 2, 1, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 7 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23246)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 74 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23247)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 6, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 15 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23248)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 2, 1, 6, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 63 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23249)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 99 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23250)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 39 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23251)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 62 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23252)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 3, 5, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 2, 6, 1, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 59 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23253)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 6, 2, 1, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 8 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23254)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 3, 5, 0], ![6, 4, 1, 5, 3, 0], ![6, 4, 1, 5, 2, 0], ![6, 3, 2, 1, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 53 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23255)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 0 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23256)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 38 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23257)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 11 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23258)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 11 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23259)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 73 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23260)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 16 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23261)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 6, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 16 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23262)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 6, 4, 1, 5, 0], ![2, 6, 3, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 16 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23263)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 6, 4, 1, 5, 0], ![6, 2, 3, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 16 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23264)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![6, 3, 4, 1, 5, 0], ![6, 2, 4, 1, 5, 0], ![6, 2, 3, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 68 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23265)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 56 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23266)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 49 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23267)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 84 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23268)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 2, 6, 5, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 1 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23269)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 3, 6, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 34 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23270)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 66 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23271)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 6, 3, 1, 5, 0], ![4, 6, 2, 1, 5, 0], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 79 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23272)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 6, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 66 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23273)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![4, 6, 3, 1, 5, 0], ![4, 6, 2, 1, 5, 0], ![3, 2, 6, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 22 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23274)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![6, 4, 3, 1, 5, 0], ![4, 6, 2, 1, 5, 0], ![3, 6, 2, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 48 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23275)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 3, 2, 5, 0], ![6, 4, 3, 1, 5, 0], ![6, 4, 2, 1, 5, 0], ![6, 3, 2, 1, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 77 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23276)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 74 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23277)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 71 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23278)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 6, 0, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 54 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23279)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 6, 0, 5], ![3, 1, 2, 6, 0, 4], ![3, 1, 2, 5, 4, 0]], proof := .tail 74 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23280)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 6, 0, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 2, 4, 0]], proof := .tail 54 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23281)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 6, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 2, 4, 0]], proof := .tail 44 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23282)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 6, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 82 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23283)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 6, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 2, 1, 4, 0]], proof := .tail 85 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23284)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 6, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 4 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23285)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 6, 1, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 2, 4, 1, 0]], proof := .tail 65 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23286)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 6, 1, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 70 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23287)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 6, 2, 1, 0, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 52 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23288)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 6, 2, 1, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 52 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23289)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 4, 2, 5, 3, 0], ![6, 4, 1, 5, 3, 0], ![6, 4, 5, 1, 2, 0], ![6, 3, 2, 1, 0, 5], ![6, 3, 1, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 50 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23290)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 6, 0, 5], ![2, 1, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 100 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23291)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 6, 0, 5], ![2, 1, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 11 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23292)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 5, 6, 0], ![2, 1, 3, 6, 0, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 4, 0]], proof := .tail 93 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23293)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 6, 0, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 4, 0]], proof := .tail 12 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23294)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 6, 5, 0], ![2, 1, 3, 6, 0, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 4, 0]], proof := .tail 81 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23295)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (23168 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 23168 ≤ id.val) (hhigh : id.val < 23296) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 23168)) = true := by
  let j : Fin 128 := ⟨id.val - 23168, by omega⟩
  have hsum : 23168 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (23168 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard181
