import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard162
open N4R2OuterLeftReplay

-- Cycle fingerprint 0043b988629118d2fdd7bc5cffb169376fcfece2c5bce2c8375a56ac02fd765c.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 5, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6]

-- Cycle fingerprint 005b5ccab423e53ae5306d979d451da5054e75600446aeccf9d7923792c5c22a.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 0081db5c65a5d5faf6563d2b89c4d85504ef72060f2993de5206f69b9965dfc7.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![0, 0, 0, 3, -3, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 3, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint 02a7a9deb57a37ab6c8a6ff9811f2560d6d67cabfa82aacb55f386f542b00fab.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-3, -1, 3, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 4, .corridorLower 1 4, .corridorUpper 0 1, .triangle 4 0]

-- Cycle fingerprint 0310ff91b2389153a1c2728f6df594b74a2179188755e0388c2847cc91b9632b.
def localCycle00004 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0360de598970a04da760241ac52f817e5d7920433f75f720a9758250016bd25f.
def localCycle00005 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 091d410ef971085aa1cc58eb367421e9d816adab147e09556928f809b27b8e98.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 0ff3103f1a272c7d937a1e290e7325c3216e676c450c9b786370e87b539fe369.
def localCycle00007 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 137c2b38d89078399708785099fcf24b7c8a77a00d19e4ca40cbc1288c28fb2c.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 13e67eab18c074bea7f6f2180de2896ef8e257b206e4e41b49231d368dcdd80a.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 16 1, .gapLower 1 2, .triangle 20 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 14848c6b3787e59d7dfd3aac1b9350d8f99226505b0f77b657003c984f666681.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 14af85a7808fcf7075f15f3b685e806a90e6d317237e490de7b136e671ddafb0.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 160161ac7fa5bebebe4513de3364d7d84ed1f7ee8c7a600fbb3f67d078b329ee.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 16d18ff0e40694cf2174b2182797d352c8c705cacff04f127ab4f20a87ac543e.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 2 1, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 179a23178912cf1459ee19d36a1b2aea640ec110c0ca68f480372d6b5b24861e.
def localCycle00014 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 197c0a8b5d419b556c669f1b02b02bd187e79f37d9e599f293260f820deb7e57.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 23 1, .triangle 16 1, .triangle 17 2, .triangle 20 1, .gapLower 1 0]

-- Cycle fingerprint 19da9aa7cb721e5f831e9ed7b1c45744e5c6e91a6e928978ed2848cebbe07a79.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 1c4cb1bfe3f135919f8292ae9515a64d496a5c9c306d6f44837022869895c958.
def localCycle00017 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 1d8258928e245fe563fe66881095d7029ad5b77967f350ab845ecf359f6ffd13.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 0, .triangle 16 1, .triangle 18 0]

-- Cycle fingerprint 1e0075996b9f8e10e3d89b87dfc7c1902d06222f1746d9a35ab7c76158b9336c.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, -2, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint 1e4450f8aca65a25b95447e63776fb27984718fbbcbec9277930bcf682ce83d1.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 1f7041fb84635be0fa2e9ef672bb9eb31433111d32032a313e49a2ebfd9d3270.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1f805dde4ba33a959704b0ae5d4f112579be0a86d491975ac1e5eea359dbf222.
def localCycle00022 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 21db27827e26de456d031a84ca05294c16145e2b71f654b2261bafb16cecda21.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 23 1, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 2271792505b3d075c2f96811bbfcd13d40da03b670a116a5e0bb030344a91492.
def localCycle00024 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 255527ed1b79836d493bea8a74748503c5a06439d3206ff8c6cfdf870a9f2bdb.
def localCycle00025 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 2689eb3d6c3b990967e3f0f1c5127b78565ccae8af730d474e49ca38272b3864.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 2703738372c87b6bff7c5aafd63aa5ba2054d10e1afdfff1d93cedfe028f8ec0.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 2a9e41702a7a9443b1f7b920d833b1a4d98b9621cef95ddc4d9d41d9b3193841.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 2, .gapLower 1 0]

-- Cycle fingerprint 2b7276de24447c1ef75ad330bc04e16686dda4cfe2c03cc0cb84f92cfb861a95.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 2c238d779c1b83513a35360d76ca948aec193c733d43841c03586bb2961665e1.
def localCycle00030 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![0, -2, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 20 1, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 2c6ed92151f6672be8cf994dbc20aa637996ae9b241767809f3b23fd199ba6f8.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 2c8ba1bd97294565d66dcb92d453df289fcfbbbfde83009ebda34cc9b032a43e.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 2]

-- Cycle fingerprint 2ccebf4e680cc1d8eefc62718a6f19a212e34cfff52377f7fe0fa099825c6854.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 2ff6ba61c17f7cceff47f0e62ee366f3079e3ae29e50eb1a182d52b3a23a3849.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 32a3fa3c7915c3c62b27dad87708ce372bb816455bf63b9d3eff9b607cbdd1fc.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 3319e7f235c35a301b70755688231fcfa086a00f4ea8fdfd089f0e4e985b07c9.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 23 1, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 340e9a43cdaf6c133efb9857bf91540f93fa25e7fbe710d3ed5d920f3217bd6b.
def localCycle00037 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 34f69b0df51335fb10141c2f0a8123774323f36dc7069454c8076a0de6858fc4.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 16 1, .triangle 18 2, .gapLower 1 2, .triangle 20 1, .corridorLower 1 3]

-- Cycle fingerprint 35c556a5b89d3a8ae20058a3bba746e64da62f7c1460a369b68a54f8639c3937.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 36e02581b151badb3285397f6409388e4b235dfc51a4f8ba8a86c9bc3d672fce.
def localCycle00040 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 37df33d588f16b1b915530c36a442baa5ec95737831b38a185837706d68a2bdf.
def localCycle00041 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 3ac797035fdfb542ba6d48e9afd1c14aa41f272a172dcfae406790ec5dfdc97e.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 2, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 3beef7508e20b7b1c1d09c483b9f5e5f5994e1dd261ae7b0b617c8ab82d4fe9f.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, -2, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint 408ae19361f3af219a1529320f40a6fde7ea09b24ee8b4996b4825632de2f9dd.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 4294fda3c0a392ec507bb69b5941111e91aaef88a573b206c9fdef1d6f955ef0.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 44375e4f4f104d8e6069ee562b8660ddfa30a1cdddbe8d00289e5987f7e5f5c8.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 454db32997111d1f6ad76e7f7792f819701fd87ccdd7cb6c232c47dd3789dc98.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 47a7721c940d244510c23ad0e243857c7e219c9db4ab25586981285215b0aa02.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 16 1, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 0]

-- Cycle fingerprint 486a31af1b6852f80f5bb37f37da1b725b07f724a8fb0172f731ecd679061650.
def localCycle00049 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 48b422755bef84bfeb4bd7c3de8e84172cdca26f9e6f033ca410b4d2908ed666.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 494d7adbfd4e25635b5ed8e9470f46d0fd6478e017fd5ebe35d84c1ea47690fc.
def localCycle00051 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 4a6a61f4852f4bb03a2ef3aa166ae6030fd3814e57d3ae3bda085fc8dae5efbd.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, -1, 0, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint 4b1d77da659005ee6751e184b5c226608db0f36ef93c109c360f14c066a414cb.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4b6a54eb25135289bbaf9b812af32f813a00fa1ab8e35eb1b1db68faa4affcfd.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 4c4d6465ffb2e548bc0ad0695af8358f850a7d516d682b0c2bdbd16a87f9d072.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 4de22bda0d4cf1109278c7200e02f78e691971ff51676d0c16874801edb3427e.
def localCycle00056 : Cycle where
  length := 14
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 0, -1, -1, 0, 0, 3, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0]

-- Cycle fingerprint 4ebfe870e226f09959e04c462c3e3f17770224a92c74dc38bf1065a8e5e9e535.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 23 1, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 52951dfae8b301589c56bc01d383d20798b88bf19c97ff6c2765838f0a558d65.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 529c01a041236c995e6a5c12e152c759288e1307ef4338f5216550c8c5a60e4c.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 55e6e15e903d310ed8055b4d7144f337bbe4e6645a0045baa88a45b677a08aa6.
def localCycle00060 : Cycle where
  length := 17
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 569cecf0821d1572f6c3f0401365aaf9b9677c39fe468af76fe6c80d0f36310a.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 56aef1c5a2b2ec1845b8316c045a081f3256140c8b90fbbf6e71f63884f5b153.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 0 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 58780297f4bc493fa6159dec28b883ee69c26dda1deb0a1f54a1c167e41e8c69.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .triangle 24 1, .triangle 20 1]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00064 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5db3f22859547724f9a1020b238b5f032a7200ef04995a604d3f5b4ba907efbf.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![0, 0, 0, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, true, false, false, false, true] }
  origin := ![.triangle 23 1, .triangle 16 1, .triangle 17 2, .triangle 20 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 5fe66d23de56530aeb228f33bbc7f9714ddf719b559f0e7974cd1ed4b8ac5f4e.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 4 0]

-- Cycle fingerprint 6002ec222e0b6f6351641ad47a6577b89318fa8903e8d727f1d963d3d57b206e.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 6320cadcf4bb3417d3b13934efa0503a3d6c3330c8747a3cbd306e93d4105cd8.
def localCycle00068 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 6a08ffaebc65c539736a9c6c897e802815e3e79f3393c300a518bea0461af33c.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 6a954460bb0fce0431c2e9daead0714df4b7f1da08a166713a411a6c6c65d781.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 6be751f562ee619bf645462c3763a2ba2c4e63e5ca5c1bdae66be78b2b958472.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-3, -1, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint 6d65f2bf6348f44f0c1f636e7afe6ff31a74c655019c85a4b4f30064ec3d8815.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6d9d66769d413414b6ada7cc6578d2fea6339af5fb43deebb38b327b0e7c1780.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 6de42970bb4337b2bcf719a98a4d47624fba0a06c3c7860486c583eb6d225896.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 6fd471fbf8bd0b8d3e4e97e43258206ddd983ca83d5b373d6eacb0ccd092888f.
def localCycle00075 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 23 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 74216db6be92ddd1642000c9dd305376f0aba525be8eaef43d13dafe8a02b579.
def localCycle00076 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 7571444db0cdacd9942eca4ed23d75dde93fdabecbba8b11d4f31090207ecf2b.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 760ee6ea7fd7d5fc28448ad6d8696ec63211ff1ec09eb2fceb4416687fcce60d.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 774af9af8800caf1e5d873be18cfaa414ae944e913ff6ad0e84761efa82f20ff.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -2, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2]

-- Cycle fingerprint 7776fff64628298833319306871b732fd65d54673336fb0cdb29e4260f56eaf2.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 794ffe77e337c7896374d3e7364dc761332aacb5e9f2c073b9f53c878b47dad6.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint 79548f12d1d8b9446cda19516ef1e178ef0995495eb42758195e559c29ef0e30.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 7ae405a6e9b0f59c9358d551a19dc946921350d8ef021fb2148e68317f0cf170.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 7d20e1c23a9a511d30c8fe94a9df124acecce8848b0a83a27ceda5af17412d73.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 805ead36e987cee0bd87bc09544fbd2deb77052be86cc8008618b4b9d67512a3.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 2, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint 81427d2c78f03357e25cb8b2c043c7a1e3b435cde1d8656cc1b5fb9f6de8aae7.
def localCycle00086 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 4]

-- Cycle fingerprint 824a07a24483f92517652d434a745a926734cc0ea06019cf8b1093aefbbe17b3.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 828949d93b0377b3456fde9e49aa35271937c3b39a96bb9441d945bcd949aab9.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 82b8635fc1f72a6f45db70fc01e00aac7d7592f4e2f82dda070ec9468dfbbb70.
def localCycle00089 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 16 1, .triangle 17 2, .triangle 20 1, .gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 833afcee5456b98b03b68a3c5748bca445172caa42997b08d7ffe47752cbbd6d.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 84da59d679222a3f02303e7fa5be3548cfd3804c20f1a12aafad38746fb4831d.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 2, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 8648faf7b4f1b5bbb63693bc600f7a9c60167fb4ec82ee19f627d06690598b82.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 87358465204b25a72e3a4722c8d785165fa7f145c43a881b6da713212ceb9a00.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 8843fdad835b929d3032bb16c47709d1448be7f9206da368451e4f94b5e42c93.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 8e530950249fd7b8c9e3296a14ff730eddda42ca653a4466decc11734e5dc794.
def localCycle00095 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 17 1]

-- Cycle fingerprint 8fb7f8dd18846d746a7cc7ca92ddeb074fae2902edd1dc96d8e39f79729d337d.
def localCycle00096 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 910afa13d0101630f16286d7092bb39b9347374c3b538f35a51d4a65ae472692.
def localCycle00097 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .corridorLower 1 2]

-- Cycle fingerprint 912ab15af976fb53ebdea86db36bcf1d5118c61a782a5b39e8217c1fe2516e10.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 9167c8c458341bef8ec1cafc3e69c8661a284431aff122d17f29dee654d3e52a.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 2, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .triangle 16 1, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint 91f442b65b770dfb146ffc3131290f5d91e25130286ca2194d2ca26ad5ab7925.
def localCycle00100 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 932717fdd09166c88d5fac2827481558c9cb08721746f6905b2f346348bc0088.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 97de4fc0e94c305c014ac99e0012ea1133aad56fe2b225c507ac6675a603c55e.
def localCycle00102 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 993f1d7a71fab100bb156f5b543b3638d428502262b6682d9fbeaa683263821f.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 994210e76ed42c60da1cb5b26b77e2da23ee27e446c6457dbf9bf254022d6e3f.
def localCycle00104 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 9a908a3f506abdcc1316a4bf54061531fe5b94f88a402d6075d23c8b827f38f2.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-1, 0, -1, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 0, .triangle 23 2, .gapLower 1 3]

-- Cycle fingerprint 9b393f9d013d9c19fbd89ec7dfdb04b775122999c2ea8af866e97fd9b5eff6a9.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 9bd1bbf2eedd29285b4386797413727fa39512b92df0b64d301821be55eca1e1.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 9c3df42e51c231839b5f66103ef66f524b8a745c5e5157d9f1b89e4b91e97702.
def localCycle00108 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 9c7086e4e556d28405e0625185835c2f975b185af7c5f0c327e37c65bb1d233c.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 9c84070790f31fa33975ecb7011e98abf4224586089f0bb3a1739516dd317b60.
def localCycle00110 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9ea52041d3f66d698e31b4040f66641345a567440cc4163c1c61d2b2ac292eba.
def localCycle00111 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 29 1, .gapUpper 4 2]

-- Cycle fingerprint a04cde79f6e0dcaa6f3495ac8dce1a9d275d1487b997deafdfcc8713d4c8eef2.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a07d22a9c2736c290ecd17aa5d4b189df075a35c51670195a6e50e6cb61dbb48.
def localCycle00113 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint a2abe624873508abc7e330290ec619263c9014e610653f6b33dcc21a6320615b.
def localCycle00114 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint a587a519b5f38dcfd738d443e57d956634609ec058c85c0d8f020e2b71019016.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint a7a99078581b8908b1c3ac46abb15672b988b937535b5f4895571397e53a5743.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 16 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint a8d998d930ef48f4db8b37f582b671b3e0cf09a9d255aa9cd7216c30e9895632.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint b0056ca4b0ddcc43e88e82a89ec2fef61a7dc8bdaedace8a974baad9de8f8f45.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 16 1, .triangle 18 2, .triangle 24 1, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint b6998aa4fdec881676ff57d279ce25c86e22a97ad1d12f4f279aba56952b6081.
def localCycle00119 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint b6a1b32f71c1f3e0da3378649323ecdc216e680edcd84f2dd1d10adcdf6df5a0.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint b6b5d76555c5141e928a2c48cbeb6658af7858e03f0934c3285eb024780dcb87.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b91a4bee98649ec65352e7801f8a7a8e5a488a33581a0936ca02f359ac7d8b6a.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1]

-- Cycle fingerprint b9b49d865886fca96b7bf3d06b3e5911efed76695c610bf92fb278dc6704379a.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint ba2159936e820e3920c7e8d0c941b0bb4b023acd84ffdb6eb4109298f55071c9.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 0, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false] }
  origin := ![.triangle 26 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .gapLower 1 4, .triangle 16 1, .triangle 17 0]

-- Cycle fingerprint bc6769a1789f1fecdee7dff32b8ab21d94ca266262a745736945346e785926f9.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 18 0]

-- Cycle fingerprint bcc7d6423ca382afec9568fbc1cad7b4291f2a4858743eccb5146fd0096758b7.
def localCycle00126 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 29 1, .gapUpper 4 2]

-- Cycle fingerprint bdfb70cac395f95f7b0357ca160fa93a0d97fd1c16d2b4d8696f354fac1db0a7.
def localCycle00127 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint beb12b91ec7e2544eb5f3bfb43378bdf4fa9cc4272f359d2f7a49bd342f5f1b8.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5]
    constant := ![0, -1, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2]

-- Cycle fingerprint bf9ec8f5a6447a533a279f87e939b297d47f47bc08555fdabfcdd41753349725.
def localCycle00129 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .corridorLower 1 5]

-- Cycle fingerprint c1da733ea5bd43b90c2e0799fa770a77f5f83f6ad115d842e5951b1b3450cc1f.
def localCycle00130 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .triangle 4 0, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint c1fe0e0d4aa83e1c66529cd6ac204f1505dc9051016e45dc39765bc0cb690ac1.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint c235d938c75439ab2daf5fc237f9bec0ee50c0efe2cc3debba73a6b5c887bfc0.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint c27708eba4091d867227ae56067752fcbca0b70c155d8eda65c05a6ef8a976ac.
def localCycle00133 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 29 1, .gapUpper 4 2, .triangle 16 1, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint c6564f3b0782ce41719d5d34768a028b08f2f8790801fd66b971514790886350.
def localCycle00134 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint c72bd7f1595a62b7090841a37e68888211c207a001ff0ddbfb952b346f179579.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 2]

-- Cycle fingerprint ca549de2c8bd1ce05084dc2d3aeac9d060c95cd535042a4c44c1be0734300148.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cb2dfa605f6e2b0b79cc76c45ee715bf066f2f0957e480d758643bc0a6ddaa87.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-2, 0, 0, 2, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 16 1, .triangle 17 2, .triangle 20 1]

-- Cycle fingerprint cb498d7606254b76073df4be4c2423c7257397bf8c106cb70f5858a74e7855bb.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 26 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 17 0]

-- Cycle fingerprint cbe8ea30f2b29688614bf2c6dde7e8d36c50564539b51048daad9bba1b79d719.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cc841cc721f67d9d31e38f0e16f465464e40721f1105ec963dba2edef1eb8d85.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint ccf9ae471efaeb702d6d0fa7036bf5884259c5e2b83dc6caf1a11c332b9fb191.
def localCycle00141 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00142 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint cedb3643a7179a6c732835114823618d3b651ebcdf922064e0239b178f98496d.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint cf916b18c62be80209b42c95e8f529ad01c0041074e19d58cd26ca225342cff4.
def localCycle00144 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 23 1, .triangle 16 1, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint d026c1eb895f758c3e17bcdbb18136557728401ca75660ae65d75aa7369d00d4.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint d132190683788d578ac59a31b32b234fcbcb72e552b6544ed2e1b88b12c43830.
def localCycle00146 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint d7413fafc943b888c158ee8cb5f760139d4f539db2b52f69951aa045f2e2f6f7.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint d7ff0f6ce4ce30a8faf969a5453ceba9e52074348cc8899c18cc531965b5256e.
def localCycle00148 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -2, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 20 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint d83f3e419bcd697e0b523a19ff4a761120e7ad1228d22c263a0a2f3cd5b5efac.
def localCycle00149 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00150 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dbd544b4eed28e3795f64e026e5dc32ae783ec6805f7124b02a379cfda623c4d.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint dcbccf0f95fde8a444f9abdfccf746d38696192c79bfd33604e347eed075fdfc.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dcfbdd449d7d59a8f5d39a99649f49aa1bfaf379eb039477589fa201898de499.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint dd2b4b292c353fc86e48ce486b5eff9e41519bc110ceb9d1de5a1df28806ac4f.
def localCycle00154 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 1, .gapLower 1 1, .triangle 15 1]

-- Cycle fingerprint dd7ee148ef5de7f32800b31ddedebe34a53672be979cbdce7c3db4b7c79e5107.
def localCycle00155 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint dd887980aae9cc40ca5f3a3647de128ec62bbc0c788e662d5ec82eaa198c8d28.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint e005a1e75c0a02a6b9a5fe03222b4414bd58f861860798204a472aa3ba96f96b.
def localCycle00157 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 4 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint e0fc343796437ec56bbd73e994e73b9e6c75bce79299074088ff5e8adba32774.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, -1, 0, 1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 23 1, .triangle 16 1]

-- Cycle fingerprint e25edf239eb51fc34e4ae6f0eabd9d097352256229899a02f614270261a96335.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint e3d92162744df78efa459dd4f19068a1e0b469365afad6dc7c7c560d62cf0a57.
def localCycle00160 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 17 0, .triangle 28 1, .gapUpper 4 1]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00161 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e4f5d9720ef4d56251c8b054e17dac89c32ef5cff718aa7d1536e6c06630818f.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint e5526a5934812dffe30e1282839231e1d2d198dcd30cafcb357741d65ef45fd0.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .triangle 15 2, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint e7b625604b8d3de4fbe0bdc0a62c7843c4f49528ddf4299170f0aa436afc0132.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint ea3147b80411d263fb74d19671bba18a03fbba705681adbe18b62b078b41cd37.
def localCycle00165 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 17 0, .triangle 28 1, .gapUpper 4 1]

-- Cycle fingerprint eb7dd4fa305ecafc416eff62e95582fc0ec6ab99a079ec13efe978614f8c346f.
def localCycle00166 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint ec8fc8b07ad9247e5a178a888b12545b5e1a42d44aa990d7afeebd3139981eb5.
def localCycle00167 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint f191cb4cccf17edbf56491373011763b04479d84e0f5485b12d37fb83f91e1bf.
def localCycle00168 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f2844c1d6335cb305104b656374f169d731caaf1d32d6c858c58a10089487ffb.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint f28c613399109256220a5537ca843157e5e51acad121679a639634dce02731fe.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 28 1]

-- Cycle fingerprint f611c6b82844802432a2085d2047c6f80be9d2e32d29dea3df69c86e2b5620b6.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2]

-- Cycle fingerprint f736a19642c06d756f7dfcf9b5a60f820a3fd4e7ec6d122bd44d3ce5ba8c5498.
def localCycle00172 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint f7bf8ac974a3c74ed0e81ac78c3caf6bfce87b2deb3a3a5fa2898749d737cda2.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint f917ec9de1f23ce0ef60afdea9f490037be423f188bd4440f747d7c7dac9810d.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 16 1, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint f91c82458d8d6aeb2f69a9c596b8cc7933b89d0b61f40db70bf3b8f37eab0573.
def localCycle00175 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint fc64427346df0e89edb9adf5c0001f22c9c3dc9b550e4c82dd2bfd042970e064.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint fd26ed0095aa485243694c1fb61b93cd54cdba98c7f98a038561b1be7fc6470d.
def localCycle00177 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint fdff5d711c652e704d162c63aed2c79d5d9b609b14001bac4407365961cd2593.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 18 1, .triangle 17 2, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint ffe738d541fc223afd924d600db7949b5258e2416e2bf58e13084632867f1dc7.
def localCycle00179 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

def library : Library := fun id => if id < 90 then (if id < 45 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 39 then (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)))) else (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))))) else (if id < 67 then (if id < 56 then (if id < 50 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))))) else (if id < 61 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))) else (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))) else (if id < 78 then (if id < 72 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))))) else (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))))))) else (if id < 135 then (if id < 112 then (if id < 101 then (if id < 95 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 109 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))))) else (if id < 123 then (if id < 117 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))))) else (if id < 129 then (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))) else (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))) else (if id < 157 then (if id < 146 then (if id < 140 then (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))) else (if id < 151 then (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)))))) else (if id < 168 then (if id < 162 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)))) else (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))) else (if id < 174 then (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)))) else (if id < 177 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 8 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20736)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 100 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20737)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![1, 4, 0, 5, 2, 3]], proof := .tail 151 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20738)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 0, 2, 3]], proof := .tail 44 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20739)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low (![135, 154, 32, 129, 142, 2, 94, 164, 42, 163, 22, 91, 28, 20, 43, 177, 77, 107, 87, 175, 67, 147, 127, 14, 106, 64, 4, 82]) }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20740)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 2, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 108 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20741)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 2, 5, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 0, 6, 2, 3], ![4, 1, 0, 5, 2, 3]], proof := .low (![135, 154, 32, 129, 142, 2, 94, 164, 42, 155, 22, 49, 28, 20, 43, 177, 77, 107, 87, 175, 67, 75, 127, 14, 102, 64, 4, 82]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20742)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 0, 2, 3]], proof := .tail 44 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20743)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 0, 2, 3]], proof := .tail 83 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20744)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 2, 6, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 98 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20745)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 61 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20746)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 21 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20747)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 37 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20748)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 10 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20749)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 21 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20750)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 6, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 98 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20751)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 84 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20752)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 139 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20753)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 76 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20754)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 140 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20755)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 139 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20756)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 59 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20757)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 68 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20758)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 145 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20759)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 0, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 136 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20760)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 3, 2, 5, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 0, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 109 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20761)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 2, 0, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20762)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 2, 0, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 29 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20763)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 2, 0, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 53 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20764)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 162 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20765)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 2, 0, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 131 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20766)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 2, 0, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 31 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20767)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 96 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20768)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 78 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20769)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 78 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20770)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 168 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20771)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 152 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20772)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 0, 3], ![1, 5, 4, 2, 0, 3]], proof := .tail 170 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20773)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 88 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20774)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 12 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20775)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 1 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20776)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 56 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20777)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 0, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 152 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20778)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 0, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 170 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20779)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 88 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20780)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 12 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20781)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 1 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20782)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 1 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20783)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20784)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 2, 0, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20785)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 2, 0, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 29 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20786)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 2, 0, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 53 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20787)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 24 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20788)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 7 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20789)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 2, 0, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 131 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20790)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 2, 0, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 31 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20791)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 51 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20792)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 113 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20793)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 80 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20794)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 80 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20795)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 35 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20796)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 0, 3]], proof := .tail 152 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20797)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 134 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20798)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 134 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20799)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 168 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20800)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 0, 3]], proof := .tail 152 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20801)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 0, 3]], proof := .tail 121 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20802)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 88 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20803)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 58 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20804)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 1 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20805)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 45 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20806)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 152 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20807)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 93 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20808)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 152 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20809)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 121 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20810)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 88 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20811)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 58 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20812)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 1 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20813)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 58 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20814)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 1 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20815)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 159 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20816)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20817)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 5, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 2, 1, 0, 3, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![65, 23, 95, 160, 3, 122, 158, 57, 9, 165, 137, 30, 15, 116, 165, 66, 104, 36, 165, 130, 81, 144, 157, 165, 165, 124, 52, 117]) }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20818)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 1, 0, 3, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 123 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20819)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 1, 0, 3, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 13 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20820)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 73 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20821)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 1, 0, 2, 3, 5]], proof := .low (![34, 70, 95, 97, 142, 86, 6, 149, 166, 85, 148, 178, 89, 167, 19, 16, 33, 5, 114, 120, 141, 172, 25, 138, 105, 64, 4, 0]) }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20822)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 1, 0, 6, 3], ![1, 0, 2, 4, 5, 3]], proof := .tail 74 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20823)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 5, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 1, 0, 6, 3], ![1, 0, 4, 2, 5, 3]], proof := .tail 69 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20824)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![1, 4, 0, 2, 5, 3]], proof := .tail 176 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20825)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 5, 2, 6, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 1, 0, 2, 5, 3]], proof := .tail 62 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20826)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 169 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20827)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![1, 4, 2, 0, 5, 3]], proof := .tail 169 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20828)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![1, 4, 2, 5, 0, 3]], proof := .tail 54 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20829)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 169 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20830)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 1, 2, 0, 5, 3]], proof := .tail 169 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20831)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 0, 3]], proof := .tail 54 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20832)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 5, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 3, 6], ![4, 2, 1, 0, 3, 5]], proof := .low (![63, 71, 143, 161, 126, 86, 18, 173, 171, 17, 111, 118, 48, 79, 133, 111, 174, 99, 133, 111, 41, 38, 111, 119, 146, 111, 111, 125]) }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20833)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 5, 6, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 0, 6, 3], ![4, 2, 1, 0, 5, 3]], proof := .low (![63, 71, 143, 161, 126, 86, 18, 173, 171, 17, 111, 118, 48, 79, 133, 111, 174, 99, 133, 111, 41, 38, 111, 119, 146, 111, 111, 125]) }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20834)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 0, 3]], proof := .tail 50 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20835)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 0, 3]], proof := .tail 11 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20836)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 152 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20837)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 6, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 0, 6, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 26 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20838)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 115 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20839)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 115 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20840)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 3, 0]], proof := .tail 112 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20841)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 3, 0]], proof := .tail 132 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20842)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 152 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20843)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 60 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20844)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 3, 1, 0]], proof := .tail 103 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20845)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 3, 1, 0]], proof := .tail 152 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20846)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 103 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20847)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 0, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 90 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20848)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 3, 5, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 0, 5, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 179 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20849)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 101 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20850)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 2, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 55 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20851)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 40 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20852)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 72 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20853)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 110 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20854)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 47 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20855)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 168 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20856)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 150 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20857)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 46 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20858)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 128 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20859)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 72 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20860)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 156 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20861)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 39 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20862)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 153 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20863)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (20736 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 20736 ≤ id.val) (hhigh : id.val < 20864) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 20736)) = true := by
  let j : Fin 128 := ⟨id.val - 20736, by omega⟩
  have hsum : 20736 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (20736 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard162
