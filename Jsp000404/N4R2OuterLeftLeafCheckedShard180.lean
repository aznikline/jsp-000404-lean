import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard180
open N4R2OuterLeftReplay

-- Cycle fingerprint 02de65d543ac11f854e6b76e3113a1393989b4e858aa4b66bf3b125ce787fd38.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 0594b0aa1f174e1b2d5bb5c56f1ca94708a442f77c3f597bbb1f905a30ba889e.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 065c005d20c4105fb956b32ef38cd96151f6090598a9dadef4555d0582163603.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 06d3a5d199ee89334b1df426f1eca7173fd0f8419fd7a4bfb6db3bca19dc37b7.
def localCycle00003 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, 0, -1, 0, -1, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0]

-- Cycle fingerprint 0c29cbbc78c40593f13945396ee272bbe51980e06c73865854851276f7c80c33.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 13e078549dcc7ee38c3305589dab9c47f2a6580d59e40d798ab7139d4fdb2f19.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 1b1cf84b71d93faf8ffbd8e8a823eb71255c4f6ccad61ee46e6da1dfc189d3a8.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 1f1f212b276cc3cc0a236e4531763f536a3e2818edd66474c460dbd2e02dfd09.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2062179ee96c27951787c6d69e3351569ea30288c6db3a0e8f90e295fa967c95.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 210a86e8f4c0e1edb3fea821e3f07b19d78e5395321d32790032ca797051cebd.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 2f40642aa183900f38c9e8ad73e1519728190b7e3ba7a2a366921d2e8555d15a.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4]
    constant := ![-1, 0, -1, 0, -1, 3, 0, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1]

-- Cycle fingerprint 3003c2ec483169adb8bcc3455cc75a52088406904228d44167607ef7a817c003.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, -1, 3, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2]

-- Cycle fingerprint 3817fc5ec41d704a708673593acfd02fa8b7ef11fbca72cd85d752434e3c812f.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3bfb2750386b215253fc5b1ec39b6e1500b151121f50290818b060ccaf9880d3.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, 0, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 3ca9ee1fcfc73465a3bba8405c4e53185a38baa805f5d6c38578ca1388fbc1f9.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3d0b7884648ad16f42f1ba4856ed19d4e467d002e431e4daeb98e0a4193296a1.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 40a7f50b87b387036050b13836b3dabf3f5d5b621d82b4582dfcda90ae6e9e38.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 46c10c44ee462326df568591d825ec1368f912c5d225b04c2fdbe4591bab5a23.
def localCycle00017 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 49544d45f19d587b82b50930c32c1ea94b98b1af83fbb15ad473f72f78f88e6c.
def localCycle00018 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 49d871546a39d161a283e994b25ab2037b0f143d5027e0a3410b07e48323421a.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 4e26f772c4a9a9744c8c09e32af6d66186eff704f7f19274d01f003fdb43e7e8.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 4ea2e5d787e8f2a5d3288079de3e0e6a54842644dc8369904ea5d672ca6c52fe.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 4f0373d2b03d49ead0182153158bdc6f7598cd47afcfef4eb9f1854d24323df2.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5120f077b4a7dd450f2150880f904d595fe943cd4dad3add7d4e2bade3dc4337.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 543c1b856ceaecde0ddfe19afaa1e7d091c67db7c54911ecb2b8e88484cb6bc0.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3]
    constant := ![0, 0, -1, -1, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0]

-- Cycle fingerprint 5543cf45b840abcdf2628788bd9191ffd43b9d9836566091425c7ea288b36ede.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 588fe5f0a8c8f6d5f8dbed514ea7ecaf864ca3ffd3b10f98cca4818d38fe24e4.
def localCycle00026 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 58b0085e48ed0631a51e5be9b69cf492e76bd132af73f9f5742672281aa84b99.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5c0092b96348d37b54bee28e0993d42ef7bd4691196f23d62fb1559001532b44.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 5d9353a94204a22edb5fe40fcd97ee68804d9daa7f4420e46fa0455d44fd070b.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 5e82fd1535701ab83e153013da8f8b8516b458ad6531ddfdc46e33a45f472dad.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 28 1, .corridorLower 2 4]

-- Cycle fingerprint 62349eded64c11f2e1d5e52851a17d2ef5e954d3513aa497f53d790c3119b492.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 6aa4966aa173a3f21e19fa5e01f61bdbdfd3f251c189269c5ac2e6c8d19c4052.
def localCycle00032 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 6ff88c93a5ec77d0228f0b1a7dbfb49ba582503000b490bbf03456cd5b1416b0.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2, .distance 2 3]
    constant := ![-1, -1, 0, 0, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 26 0, .triangle 20 0, .triangle 21 2, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .corridorUpper 0 2, .triangle 5 0]

-- Cycle fingerprint 7110606a404e2618c365ac3e0ca8ffc40417df5c556d77c25ce08cc3167e8220.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint 74afd703ad75a430c013bd48ddda3e2b7d4ca93aeaadb0863244dd2180ebc9b0.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 74e9c6eb5c56bcf1bf348bf9db6f7a49153c0d59844b4575aa1625a08686b5e1.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 752463939b3f049575ac99a19044946e8798c6e1468ade79dc3a682a58aca83b.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5]
    constant := ![0, -1, -1, -1, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0]

-- Cycle fingerprint 7612415d717ac2afd2b91d09836e0343b689b6511e39566e9aeb58878f562f0e.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3]
    constant := ![-1, -1, 0, -1, 3, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0]

-- Cycle fingerprint 7e209c2563946a7d822350c23123fd2a3ccd31f5408e5afe08445903579347d9.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7e55d637b0ea3e86c1af7494f0b304be5ed8f7dea57f37588faef06aa5c4142d.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 7f5c00a4854a65d81c53867361afd993b8e931538854be69c5529173570b0edc.
def localCycle00041 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 2, .gapUpper 2 4]

-- Cycle fingerprint 842e32502e819473cc01a76b9449d50b92466f66b4f9f050eb0959f1f868d1d0.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint 8569a2f6d23090ef4a2a573a9490ad0a2f62063b44e0bfeb1ed72295ccaabe99.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3]
    constant := ![0, -1, -1, -1, 0, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 2 3, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0]

-- Cycle fingerprint 856fb9ec46b677247701e9f966e8ecbbef94150872ef1325699e1842be652c2b.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, -1, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 27 0, .triangle 21 0, .gapLower 1 3]

-- Cycle fingerprint 865f1cff3ab0751fb47f7bcad07c2c7916762d73c7f071ac85dc01eee4ec73ec.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 88a13d814bd9c4b73acebb7874ca5f2b8a378628fbe5c7334687feae92b4237f.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 3]
    constant := ![-1, 0, -1, 0, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 5 0]

-- Cycle fingerprint 8cde08edcd823de99b878e3b70d5480bd4c6536c3aefea8579f336227e95b6f6.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8e346e020e6d20af0ddc07f2a2fed619321525e7032d295a11c60bd753bd3bc7.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 8fb3aad5e06c9daf3a63c065824114577b842f42fb24997948d99e82db236f79.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint 8fdfc9f8fa6015cc65795eed5fe9a950b39dfc2b1a6cc90125066ac89d483b47.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 971f7a939f15fe0ca579a6eeb5d3ee4972fe25cf157246db0b03c571dd95e27a.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5]
    constant := ![0, 0, -1, -1, 0, -1, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0]

-- Cycle fingerprint 988543e46223bf3941f7be7f35cc4fbdd406524fd55fb2f9bb6ed1454fdeee00.
def localCycle00052 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6]
    constant := ![-1, 0, -1, 3, 0, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true, true] }
  origin := ![.triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1]

-- Cycle fingerprint 997e996015f59308a08206b00eaa02c1253a7eb1cbf3b6c9bf424b2db727427a.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 9f05ccc903dd1ec1c487811e425bbfc9f86f3e1196b58c53ea0e4648cafa5f4c.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint a5d1dabc66bac29117577a0934d64f500a9c0b678893c2c7fd44b63e25d7d2e7.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3, .triangle 18 0, .triangle 29 1, .corridorLower 2 4, .corridorUpper 0 2]

-- Cycle fingerprint a98ed6ad8b513b6ed1480027cb3f93005c790b1e8ad1433c7c817fa88cb7b813.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 15 1, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint a9b3e5fce5cfc0cfcf58b609f470b44ea835efbe8cfbdf6ba54d30399a07b042.
def localCycle00057 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint aa2e09023e6337ea231f15b987c3e537fbc199b511750bde1a82ccd700c9b27d.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint acbbb835908983d7264186af54c61e209d1a508bbe8a48926315136615037fca.
def localCycle00059 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint adbc87928d07dcb206d9cc682226e3b73002b23599695efc12634e65bc269e30.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint aee4c0b6cb9ab8b183011ef3d162cb02d7315583937d73290e7d3c9aae1ef9d2.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b533008b9802949640c81de364ff142790f8af440af2f674d58064e76b23feb5.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint b5f18dd101db745ca586cbdc8333614fe2a1ada09d34a57332bc9807e669a9ae.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5]
    constant := ![-1, -1, -1, 0, -1, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0]

-- Cycle fingerprint b63c319d6609c5a19ae60a15d3580b419b1c90d479ff34472034ba611b9e959f.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint bbc872ab798aeac2d5a5f534280d546ae121ad4710cae7ad6ac96c16ece7de41.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint bd25a26367e7c7008147bc09d15f5a41d50e080e488d448a1c23a1c2b414f8de.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint bd5befde73ccea303208aa133cf6dddd0e3ff7a9e1de401684067b60b322aede.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint be1e4748f984923604079a77b9ded57ffe647249f938abbd149ee70a92f71dc0.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Cycle fingerprint be2d106face09e009fb59cb4f7eeed0d26de46d03fa65dbcc81ad573f0cb35aa.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, 0, -1, 0, -1, -1, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .corridorUpper 0 2]

-- Cycle fingerprint bf463f6eefb6a8fcb6fa408c36782a3823b0fc8a3786c0276e1d216757426343.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint c0b0299137090ddc18f22ec7a99752d6abd4e43638bc9070aa6e5cc55a751413.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint c7b63cec5e2b9bde95d8d34286a88138748f245cb0d9c620b1548ed25fa5cee6.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Cycle fingerprint ca4cffcf4773e07b23c0ae94a1b41cb35a12032a7558e04b9fdfc3a25cab2f2f.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint cca92e2297cbfe6b9d7cf3dfb4f95a56b93e8d425e1a0268a5816f7a098792b1.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 1, .corridorUpper 0 1, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaLower 4]

-- Cycle fingerprint ccc9980dfb6ff048c4ed5152c55bcd4c70486d56edeba54b476867b29664302a.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d0ec1693701641e670facac3cd54c66735250668c9cc9768f930d71e54422550.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -1, -1, 0, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2]

-- Cycle fingerprint d19800db2a779e59fc90af6f228f4777230fa098536ccffdb536bdb48538f412.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint d25a8f731a605dc7a9d9d7e36df60541dab30d6cd261b53e2b7f0ad5e02361f6.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint d393b5a71bf3b7ae23b0504940e78174ff7690295734373f2d0ea84f32246d0d.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d674e91a51d1a29b21ad150a825719ec7aa295ebf286419dc790e3e9d16a0383.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint d7088a06cadd56ad64886f899080791d4f37f892475c2b279167f20c882b13ed.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Cycle fingerprint d73d8ddfa554821acd0e778a7869d28d97d6a8f7e378f3e4e04dfde09ddff753.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d7700ec118e73787fba9e54735cd2c5948a971eef7f5c7ea2c1c2c4165321d26.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint da52987c6881fb5be3b7070310dd4908c05aad8a8a541337e819d2a722c04805.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .triangle 19 0, .gapLower 1 1]

-- Cycle fingerprint dac71287aaf94ab1d31a4583f25d48d7ca94fa1bcace53b2f183fab74014069d.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint dc74f8f142d6ee9a01be9ab89a19573c169902323d6403ee4f325b5db69aa66e.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 3, -1, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 16 0]

-- Cycle fingerprint e0731f86606746fe0ec03d0ada878479b5682e9a345b9f8dc848939b5364c974.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e10b65ae62bd8f09b34fca0238896b456f10ea9b78be7ee240c458b871f3366c.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6]
    constant := ![-1, 0, -1, 3, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint e45a6d0f6c411af3dc06aa25402105ade1ab47e49955fb310c7c85e6dfb0c23e.
def localCycle00089 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint ecb2b1a1d9c17e71d6dcc988750d6c97fabc7addef98a5c83770ce6fbd70eb77.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 2 6, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, -1, -1, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .triangle 18 0, .corridorLower 2 6, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint ee5907b9c5ecfef97ac69ea82ecf48d446d8f38fafea0fc38613f11738d83dbc.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint eed1d675936cedbeb1e9cabbaed77dcbab92b830eb4a3a4d2f58aedc478fb309.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint f90d4e74710ff2a3adde9b4c9791f6d73eb30617831d3ff63ab9eca26477944c.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 3, .distance 3 5]
    constant := ![-1, 0, -1, 0, -1, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 5 0, .triangle 26 0]

-- Cycle fingerprint f964ec1db25e9a818bbb4894eb59ee9cd2422822f373ecf4249f0b204518fbfa.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint fb0be345b4dddd62fb7958d7269d41775aa59632a2d01e4d99c1690cb5516e40.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint fd2e4ce77ff8ec531465c0bb41bc55f4412e9a72684f64010e99b75d5f3b8470.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

def library : Library := fun id => if id < 48 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))))) else (if id < 72 then (if id < 60 then (if id < 54 then (if id < 51 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)))) else (if id < 57 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))) else (if id < 66 then (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))) else (if id < 69 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))))) else (if id < 84 then (if id < 78 then (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))))) else (if id < 90 then (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 48 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23040)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 20 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23041)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 36 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23042)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 36 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23043)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 32 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23044)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 8 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23045)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 48 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23046)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 28 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23047)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 89 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23048)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 5, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 48 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23049)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 0, 4]], proof := .tail 28 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23050)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 36 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23051)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 8 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23052)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 6, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 89 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23053)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 6, 1, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 35 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23054)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 6, 1, 0], ![2, 3, 1, 0, 6, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 0 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23055)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 6, 5, 1, 0], ![2, 3, 1, 0, 6, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 41 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23056)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 4, 1, 6, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 36 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23057)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 4, 6, 1, 5, 0], ![2, 3, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 8 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23058)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 4, 6, 5, 1, 0], ![2, 3, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 66 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23059)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 27 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23060)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 17 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23061)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 49 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23062)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 3 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23063)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 69 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23064)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 67 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23065)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 5, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 70 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23066)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 56 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23067)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 49 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23068)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 21 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23069)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 5, 3, 0], ![4, 1, 6, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 93 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23070)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 42 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23071)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 33 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23072)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 34 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23073)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 67 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23074)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![1, 3, 5, 2, 0, 4]], proof := .tail 86 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23075)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 5, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 6, 0, 4], ![3, 1, 2, 5, 0, 4]], proof := .tail 67 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23076)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 5, 6, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 1, 6, 2, 0, 4], ![3, 1, 5, 2, 0, 4]], proof := .tail 86 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23077)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 1, 2, 0, 4]], proof := .tail 40 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23078)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 2, 6, 5, 3, 0], ![4, 1, 6, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 12 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23079)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 3, 5, 0], ![4, 6, 1, 2, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 81 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23080)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 1, 5, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 3, 2, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 55 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23081)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 1, 2, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 79 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23082)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 2, 5, 3, 0], ![4, 6, 1, 5, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 1, 2, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 4 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23083)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 30 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23084)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 1, 6, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![1, 3, 2, 5, 0, 4]], proof := .tail 44 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23085)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 2, 6, 3, 0], ![4, 5, 1, 6, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 1, 2, 5, 0, 4]], proof := .tail 7 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23086)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 2, 3, 0], ![4, 5, 6, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 0, 4]], proof := .tail 82 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23087)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 2, 3, 0], ![4, 5, 6, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 0, 4]], proof := .tail 71 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23088)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 3, 0], ![4, 5, 6, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 87 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23089)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 2, 3, 0], ![4, 6, 5, 1, 3, 0], ![4, 6, 5, 1, 2, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 94 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23090)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 15 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23091)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 47 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23092)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 77 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23093)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 2, 6, 5, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 2 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23094)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 31 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23095)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 60 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23096)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 6, 3, 1, 5, 0], ![4, 6, 2, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 3, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 72 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23097)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 50 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23098)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 25 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23099)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 75 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23100)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![1, 2, 3, 5, 0, 4]], proof := .tail 96 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23101)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 5, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 50 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23102)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 1, 6, 3, 0, 4], ![2, 1, 5, 3, 0, 4]], proof := .tail 91 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23103)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 1, 3, 0, 4]], proof := .tail 54 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23104)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 3, 6, 5, 2, 0], ![4, 3, 6, 5, 1, 0], ![4, 2, 1, 6, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 14 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23105)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 1, 3, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 60 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23106)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![4, 3, 6, 5, 1, 0], ![4, 2, 6, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 60 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23107)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 3, 5, 2, 0], ![4, 6, 3, 5, 1, 0], ![4, 6, 2, 1, 5, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 1, 3, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 23 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23108)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 75 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23109)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 6, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![2, 1, 3, 5, 0, 4]], proof := .tail 61 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23110)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 50 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23111)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 85 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23112)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 5, 6, 3, 2, 0], ![4, 5, 6, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![3, 2, 1, 5, 0, 4]], proof := .tail 53 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23113)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 64 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23114)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 65 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23115)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 3, 6, 5, 1, 0], ![4, 2, 6, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 62 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23116)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 6, 3, 5, 1, 0], ![4, 6, 2, 5, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 95 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23117)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 6, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 1 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23118)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 5, 6, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![3, 2, 5, 1, 0, 4]], proof := .tail 78 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23119)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 6, 5, 3, 1, 0], ![4, 5, 6, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 1, 0, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 5 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23120)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![4, 6, 5, 3, 2, 1], ![4, 6, 5, 3, 2, 0], ![4, 6, 5, 3, 1, 0], ![4, 6, 5, 2, 1, 0], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 74 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23121)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 5, 6, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 39 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23122)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 39 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23123)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 80 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23124)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 39 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23125)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 76 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23126)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 10 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23127)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 52 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23128)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 39 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23129)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 76 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23130)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 51 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23131)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 88 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23132)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 37 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23133)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 38 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23134)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 83 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23135)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 5, 0], ![6, 1, 2, 4, 5, 0], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 45 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23136)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 26 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23137)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 84 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23138)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 63 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23139)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 29 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23140)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 43 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23141)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 59 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23142)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 63 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23143)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 29 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23144)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 43 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23145)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 9 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23146)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 57 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23147)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![6, 1, 4, 2, 5, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 73 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23148)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 3, 5, 0], ![6, 1, 4, 2, 5, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 3, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 73 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23149)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 18 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23150)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 4], ![1, 3, 2, 5, 4, 0]], proof := .tail 6 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23151)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 2, 4, 0]], proof := .tail 11 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23152)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 92 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23153)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 4], ![1, 3, 5, 4, 2, 0]], proof := .tail 24 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23154)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 24 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23155)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 0, 5], ![1, 6, 3, 2, 0, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 46 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23156)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 58 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23157)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 24 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23158)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 13 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23159)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 16 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23160)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 68 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23161)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 5, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 2, 0, 5], ![6, 1, 3, 2, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 90 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23162)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 5, 6, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 3, 6, 0, 4], ![1, 2, 3, 5, 4, 0]], proof := .tail 22 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23163)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 22 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23164)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 2, 6, 3, 0, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 19 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23165)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 5, 0], ![1, 2, 3, 6, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 22 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23166)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 5, 3, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 4, 5, 0], ![1, 2, 6, 3, 0, 5], ![1, 6, 2, 3, 0, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 19 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23167)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

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
end Jsp404.N4R2OuterLeftData.LeafShard180
