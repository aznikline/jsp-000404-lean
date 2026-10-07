import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard145
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

-- Cycle fingerprint 02e34c8b0e3550b29f8e03d28ab1587d213cb0e6ec4205ec5562c001efdf1889.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 0, .triangle 33 1]

-- Cycle fingerprint 02f63000dc097fcf652301e7df6daf5f2f7619959c920d971da59e4ad32bb29e.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .triangle 24 1, .triangle 22 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 063379bc7933ff612ea4d7f546e49ee0f5f53297ca3dbfaf8f20d356f0c2b02a.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 07b5afbbda6b84dc0a34fa7873addb120f5c6ffb27723ff0b8809aae3311f7ec.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint 0a0069b6f48faea17553917fc11d118a022f8c673e0310cf9e53fbb3f152eda8.
def localCycle00005 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 0a80b70683e00944fbeda194f2c90c93db8eb3f57e7f896cbfdf35ab705bb38b.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 0bba5f617997fee0e4ba6f77d0187777784a478696563b47f717aac83f405858.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 0ed565259a19b9bb965049a83a56cf258597cbd85c8f4288293ee84d444e01f7.
def localCycle00008 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 0f4c84ac965407fb78bca8937f15171a772e67ca7e5021003b79c7e4ae9bc97d.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 173d37de13c7b4b7f742d00cddad1619a1542ce09f87bb7db7f3e33c7bd5ac30.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint 17fb07c0582184f11c633595d694837c7d8703ec1f84c38112a055a2aa6dd916.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![0, -2, 0, -2, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 18af11667d8f121d61160e7565830a58e6193c38fce646c974f377ede9b1daf1.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-3, 0, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 1a5de4e9b8e309220ce96f91580f6f3147d81b1fbe0ce3c0be8a8fe1085946c5.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, -2, 0, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 1aaa924b080b4ce6175f52ab094ce7eaab0b95af90a4470db4b65618d2278731.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 1d8d33b2ffa92e84eada8397bfa531a24849f1ad9b563bc5077344879974c1b1.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 1, .corridorUpper 0 1, .triangle 1 0, .triangle 19 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaLower 4]

-- Cycle fingerprint 1dccd93791357810452cf98868ee3f83fc3c79059e8cc4add54c40ea97172e68.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, -1, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 1ddc6e336e247f01ab128761291579a8a38eeb4a836dd020dfbf5c9f41be8a85.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, 0, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 21c1fc6a1b16bf6a53a23c212279a01354029cd8f7297c95ef3722c1712419a4.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 2, .gapLower 1 3, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 238d200ffe99e679d3cb48086f3ca05d9a5f7269fd24a0bcdcccb6d450de67e7.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 250eb6fa73cde38b1aaa25b251a3feeb9d8a0ba9aa3ba7e69da689078e4a953d.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 270bb031985930e80f40b0c46866a84bcacbeda36b52c6f4401d42058f451a2e.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 2a248bbb1bac02b7884587c6802ac5407c727801289ea22390c7ea6c0e12370d.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 22 1, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2]

-- Cycle fingerprint 2cf6c29ff7be6488c34c2718ff7962c4a3ef3237c6e7aaf9d2c05fa24176bc3a.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 301a9b11f243c0b4fc16841766d8d7b43ff854701ba7f9a08b52ae020b122ba1.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 0 4]
    constant := ![-1, 0, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 1 2, .triangle 11 2, .triangle 13 1]

-- Cycle fingerprint 32ff5833b245d099a2c84260f417694bb805280de0cd652995a6d3af61b0feee.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, 0, 3, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 0, .triangle 33 1, .triangle 31 1]

-- Cycle fingerprint 3326e809d105197b10d2daac9c101c5c781baaf6c6d12619995b59fd73bf7f62.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 3432cb345a77158dfcdff0a3493835ae25591d86648c9df5545503afc719d3e7.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 349281970ba93dc71f64990ffb9c65c05afcfeef897bebd764d99285a754088c.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 38c3e7882459d254253aae1020d10687c134f600f1834848bb133a7ef1c1dc8d.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0]

-- Cycle fingerprint 38d209406ea9426368319f3b31d9f6e45277c26bd78694d5e3e6f8defc1e31cd.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 3b55e89a0d5c211cc85a13ad91de4fd885c59b5a6cfa5089ad954e799e1b2afc.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .triangle 22 1, .gapLower 1 1]

-- Cycle fingerprint 3bfd262a3a88bc3ea8be501463dc4e695a6f7a941754b3132ac5d4e4878d9f4e.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 21 2, .triangle 24 1, .triangle 22 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3c66383aeef95f73391cb6339ef0aefb200910a54226a845292826ccfecd1a17.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 3d7d5cf035d2ad491177a41072a3716e7e0f3c29895a404be951963058ad6359.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 3f5c58072dee87032c472ca0947054e442e98d95829318ddd2d9185f902f1f99.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 3fb4e21804583c0505aeacd7fea70264085777f3c2308b2cf06e3689eae03e93.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-3, -1, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .triangle 22 1]

-- Cycle fingerprint 41414140b04ce34b94b12752aee8a9214438bc9a3bad00ced23b78aa6de67d28.
def localCycle00037 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 45d2baaf3283c5bba9f1b682b05b728acdcc609d086acb565a9ec2d8f47c2af7.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 46c61272d5cce8f6ffcfcc13a6180f28af52238b8f77daba7eeb638a9cfcdba7.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 4899a52200f07c4e4ae53951afc67997da67167866ac65dc8998ef0f7d54880a.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 48c974551d9d456077d192d7d059d1294123de917fc7f7239acfda45b1dd319c.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 4ae0abe4bf14145a4cf37b1148db14bdb3a556469916e3c810d4302fdcb4afd9.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 4b8385bde977d92f873b1d300fb7b981e31d5404709925f6797b91de61c97c39.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4d46b2e0dfad10000bcf3995f85df654ed406c23cdb56d825813417435e5f7c6.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 50603a69905c1f19356fff811094eafae584ae55792af04f5931a30342ee19b1.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 52c67ac3a0c948b87e1c3042fa4612bfa33b6f087ad9b21aa9dc7a23e7140270.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 550089a19a1e751bab0e5f97ce0482d9388a7cd321a2b11d2c183535c7a7cc9f.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 33 2, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 56dc944d7aa8caf8263f9350be182c070d6cebc110e9cf7f6f643dc00f7395df.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint 5770175341a18b324ab2e0600a1aad72c418a9e3ec65d611d89cf284ec6ee6a9.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 57c0525993b742840e5fd4e0ee67b4830127d6ac91b318936bdd1c538dfab60f.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 5ee90054f64c0a486bea454f98528fa797a128c7b771c4a4f07a1b43bb94a759.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, 0, -1, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 60fd2c3bfcd0bdaed6bc553ba81468c1397ac606a8c7d340d46c6942d8ccaed7.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, 0, -1, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 63652464e6a1f45502ecb0c134c66e3078545f403adc236968b90fd73425b39d.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![0, -1, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint 63a7bcb796605a5ee88703f39a34e022c0dd34430d322b68b66789e800528101.
def localCycle00054 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint 654f64b0c89e45fd6875ab96f85d97ee9268ef50f72bd41210ef3f58c79c3fda.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 65ef31df02abcba2a1957c64fb7ca0f44d5ea6f0e4489a0a35d3d8abb5c6beaf.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 65f032112646c407a93da27fc4bac30c35c87771fb06a41a4cd9c5d20bee6f0a.
def localCycle00057 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 66418fa9293373ee06089a3027c038efef1d1ba6e599557b0eb1b955803e1cb9.
def localCycle00058 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 2, .gapLower 1 3, .gapUpper 5 2]

-- Cycle fingerprint 680fd2a53eff91b42d82e772929d6e97160cb1fe99d9f06af1d096eb259bd330.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 6a2a8067ce03f166893bc4765782a10ab2b6dfc56c0bbab81346e3b405ea29f2.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6c3a9b05d5ca12c4ddff80d185a4c9d838ed2494787cba56966dc38df117c8da.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![-1, -1, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 6e224d6d1df41b63091dee4d9734307e69797a8674ea5b665961084cb78fdf98.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 7149a86816bd3a0f1c7aab2219f34fbc71cb1edbd187e39adba6c5f097e0302b.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0]

-- Cycle fingerprint 730060e99e944ab942c6a2582cb3b5b49c2478d76c5dddaf1b8fd743a8013d03.
def localCycle00064 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 2, .gapLower 1 2, .gapUpper 4 2]

-- Cycle fingerprint 7345f7eaf9f3ecff1ecd4225bea9c0e95a5e8c03a3129030d90e33d43230805e.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 73bbdea7893c1e5c1e63358b5e5d3d784d20e4091e0754784b552b62bdd21bb2.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 751a95b190a4f14532a8ab2e8cd824e00d6cc9eea75646ff301a92aa19e0d2ac.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 76107fac80336720ac87df8d5de3a0ccd2ea3d80febcbb6bc60a6eda5c35f661.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, -1, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 7a2947c5403ef7bd042ffd2da8c367f63f376eae3b9f24dc6a6459070f256913.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 7c9ad723741a98286f096b0ce0b810408c964813315dffa3936b459980f013d9.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, 0, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 2, .triangle 13 1]

-- Cycle fingerprint 7d7c27d8fd21677f5128eb6f26a5686d7c8639555240fbdc62384567d0fa3fe8.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .triangle 22 1]

-- Cycle fingerprint 7dc464f911bdb5d8616b4acbbb08e24b183dbd5d184f988f04eb4459c789a9e5.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 14 2, .triangle 11 1, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 7e4762689d328a9adda100adca274901e4355c1314a50c7a96afdb8605f4dc22.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 822af656a0ea1f73dc9092a6e69753f7d7a26ed4b8f9c2c472869636d7eadd2f.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![-3, -1, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint 842eec1ad2b6d3f57dca3d58f1a75df996471aa37276a01b94e5046fb5af4ed9.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -2, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 85e2fede2d4f310a29ac80cbbe1623691bf41df62cad7a0b8e8e67021b5cb630.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8752aee558ec80b72743310c0ec57313dc8a792d8603ed883853322711a4b16f.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint 8826069bc41f788bffc10f25ee2bbac7a002fdf2028fea2fabf7d4885c64dbf8.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 8906b75fb6a99dd4f2e26f3d9d875793415aa936ae2144629aa6c70d914e8556.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 2, .triangle 13 1]

-- Cycle fingerprint 8c2c553b6ed76183dc60ad2cc32bf559de5776ad0a1dbda30fbec23c4e993603.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 8dc457602b250f2191665c512303259b6bbea3cdf3045337ccecbef2061724bd.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 2, .triangle 22 1, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 90b9c4cab1923118376dfc5be8a49c3cf894e186fb96f040a760b984627aed00.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5]
    constant := ![-1, -1, 0, 0, -3, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2]

-- Cycle fingerprint 90ed888ccd250b539b66a663bdedb717d535fb7505cbb62ebb9984e01afe255a.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 923fe6799c1b67b0709d9c6e608b98ddda6083213726013eebd84195d01dc923.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 92f40938858d72577315da1f537589459a045f9ee96e31e8e1bf72713d042d17.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 9551c369c786dce8226c9513e421c6c15a52ca9747c57b57c42c7085af461c08.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 9743c18d4971fe7fa4b4b02d51acf69d5e6842a32f3ec0f12825791be1112731.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-1, 2, 0, 0, -1, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 97a057d07048c69bebb00adbdbad1a504c5bf97a3811f0a7350547deeb6c4b98.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, true] }
  origin := ![.thetaNext 1, .corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 0, .gapLower 1 3, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 97d86820f916b07afe544ba5ad34a6a2c6bba5d8b9df96c6ae3aceaa28a3cee2.
def localCycle00089 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 9a89ec85b1b9e3d113dc6d7d1f5c5276cd467919106657342967b51bcfd752b5.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 9eaebeaed31d6e1da39d264df9ba7c2d348bc9bc0f57d0fcf412a97f7338847c.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0]

-- Cycle fingerprint a0cb4325842ed3f8dafd73464f2511e4fa2a9193291d80672178821f72967117.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint a0ccc21fbbbbc87d83a05b6a7b34869beccab82b6c130093681f1baf39f18c96.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 23 0, .gapLower 4 0]

-- Cycle fingerprint a4f4437d2dabf3f05bc0f4465b0d02afa4a7af3ad0fd9203c1746e3037ead211.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .triangle 24 1, .triangle 22 1, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint a579124df4edc7e635daec9d2c450b3f73b594abdd3e71b6210a7859cff69e93.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint a69344441dd065c390c4f9bcf34ff4ea1534298674b54dcb2e7158cf9afb32be.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0]

-- Cycle fingerprint ac8bc585b7435997000845c75dcf3fcc39dbe8b3d3b1137362648cfccc5dfebd.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint ad0b3147c9481519fb07b9bb21c5d40d7530cb6b9157948e5d6e90c7b12a061d.
def localCycle00098 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint add2060ba68b160591f37fa9d6b548057013785069bbb66c9e222391b964c259.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -1, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint ae53cb9f79619331cd095c6dd4253d08b56dddd1934b1767922a0dcbea54725e.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint aefd35f2ca966178b53d3a18cdbc25f8d8a2d5fd21c922d12c47f56b2eb7ce6c.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 22 1, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2]

-- Cycle fingerprint b08d5d55a7d402c02568d5843a9ccc16044827495f50852d3e409589fdb4a794.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 21 2, .gapLower 1 3, .triangle 22 1, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint b0b7388694459ba4db70bb997e6972ca7a24aabc1a0990f17bb055a1b580f82e.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint b3a7f7cbf6f755ae9f52a074d321b8ad2dc3d90cd7b342a42a92e4e0cb05b245.
def localCycle00104 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 1 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint b6ccc6a2b20c96a6aaae2b3e896db1d980a5fa895651f6657f1aa902fe036504.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .triangle 24 1, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint b8168f7990f578c5a633d00e9f5b59aee4be457994c535da2884df8b01df59c3.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint b8d66862cc330790161061c9d02bd4b3494ba6459f3261a4257ebc71860e981f.
def localCycle00107 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b914a04875383fee3f579325e82f32299f33e04686bb8cf1dbdc1c2674601ca4.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint ba027306af588586541454e2e771de5d8aee63484032af7d63bf4364f69e01ed.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![0, -1, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0]

-- Cycle fingerprint bb59bef766d18dfb43b5dfb20adbd69ee702956e97e58eef1be36e343a795366.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint be2f948562e0c798d26f0fe1338b2534b8bd3e2825168d0dba85bcfd86a17d6b.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint bef5134f517be701b349b0854dc242d1f751292a42195f1591c4541c8aa7e8dc.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, -1, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0]

-- Cycle fingerprint bf445d76e114c5950cbfde6f86fbc6280dfe954e800893dd5402c7f2132f1077.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 0, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint bf89759eb8df8fd738567ec8d72a87de96977f72fb807e57e865d460ecd4eb99.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![0, -2, -2, -1, 4, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 2]

-- Cycle fingerprint c068116344f39ff51208b3b3217c24a529cb86db7a78b67855c9feb1584e236b.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![0, -2, 0, 0, -2, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint c2e64ebe3f6ad3abf9fe32748c069d0ba97b69fddbb4b4940445e638406335b9.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c31a5a7bd79ed070a5e764c7b8680857dc9a160afa540406077fd56d7d89e472.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint c584a309e6468738b51a118e17f6cba1c167a46dd654aee87c9e99d33654118c.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 23 1, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint c78e09c36189090a82d8222a22c872b54da211b712ffac907b048bf434b224c8.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c7f2ee99b316b0c3f513e8e2516149724dde80a796ab0fc387e8577d0bfff897.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c89c9b410b48916efb1f64756328f59e0a274c752ab2bfd1b870a24b43545a2d.
def localCycle00121 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 3]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 21 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint c8a1bcbb9dc54b021aaea8238645cf18d6294a78c04c283a50718242e46e61a8.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint c95cb2e7c13c9619fb170fb335b20d6b7504ea8dff60735ac134ef5b2da743ab.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6]

-- Cycle fingerprint ca373e1870aabda45e1637d557c64e25c34a13d92a08bae42e1d3167c8fe9f73.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint ca52816dc1c1187402669d6f664f215d6c96901cf41f2092ebc950882e40c225.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 16 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0]

-- Cycle fingerprint cc060dce73c8fd118a3a1465d0ec3d57283f496b4f70a412459a226eba82dcad.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint cdf2f4817d636346430e4af93d1adb1cd9fa0f0f5f484c96bb5eb8093268dd4e.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 0, .triangle 21 0, .triangle 33 1]

-- Cycle fingerprint cee51fd81ba6fcd183adb53809cbfa89056fe4cc9b1e51d735c187197c430207.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0]

-- Cycle fingerprint d27c3e16533910830d96a4103cafcae98131ff0262851879c8f662f017a148fa.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 2, .triangle 11 2, .triangle 13 1]

-- Cycle fingerprint d3187b71694739464c953c54220a8d6d75b43e6d874d4ee876994a366ad9005b.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint d3411e3016dea52e9843c478d81cca04ac38ab9c708bbf7d6dd44a94ab3cc047.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint d369ba5f25cc10a5d8dac6ea14088133f9e0b34027659e1c0a581e83e2cbf846.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint d502fd90f6ad279f358a7fb14d9f493fa013a0d14adeeb73f6c69098f11ca158.
def localCycle00133 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d556b3f93eb3a69c143d5283bcea67e8c99b8dc0b0b95dff69c57092723ff74b.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d63af49b62be28e5c4bb9d37843aa56e8d2400412a4d0b6b10c6c7b85b27dda5.
def localCycle00135 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint d68721744c572ff1d5ed06dc27bbdc8c6bbb897dc687d3b4a50330fcdd2bbba7.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-1, 2, 0, 0, -1, 0, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint d6de72a1d835151b50b854bdef41625f60ec9f2903ccc088c20cd3297d8d59c7.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d75d60ad6bc0cd9ab37021cd3a056d5814342108a7aea2c1abd562310cdc7794.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint d95e81051b13935851dd08feabea785c4087b5edb244617213dc72941d1730b1.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 3]
    constant := ![-1, -1, -1, 3, -1, -1, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 20 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 0]

-- Cycle fingerprint d9a338befbfe94a459711dc729216c3061caf5a27408388fc3e910ac83ab22b2.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint da588134e6cc0eab58f1c6dd09a5ec898470fbc20349b294a59a69ccd17a9398.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![0, -2, 0, -2, -1, 4, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00142 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint da8bce17f2a93c850929715275ef507b31b27518bf3ecb2146396e00f2282b08.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint dbde3065a8ff7a4f531371977eebeebdf89cc329d785488b0e27fbc609f31c63.
def localCycle00144 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dc001319960936f631e7aa3f289e831aba25f308cedf61cbe07d4f48b5dc3112.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dc3bf29d806a383dbd964351435aa12b202e9f0d51782622dcf4a85bad675f29.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0]

-- Cycle fingerprint dca8ead6353f3dca8a946fa1a5e390077b94eff9a84fab04a687783fe767ff87.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 24 0, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint de9bdce07679f6bb71d1c43f04ac427939d2d53c833776a950a78baac441582e.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint deb71d55929dff3393590eb5ce7d8ad586fb473688affe7568fc360fd869050f.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint e1961f78f6ddff01d005c59dfde4f181af5c78eef20360cd9c6039f3409c2ebb.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint e1978c894fa3d0aee705daeee4bb900e362965d06ecb1951f46599230532153c.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint e4428a657a72fa5f6ec54bd9a34b84d43252dac0533bb66df91da2d9166db938.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 4]
    constant := ![-1, 0, -1, 0, -3, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 1 2, .triangle 9 2]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e860972e9774bf98614364325b677812e808f1633bc41e1af178962fc7fe2fc8.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, 0, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 11 2, .triangle 13 1]

-- Cycle fingerprint e943663c7d8a4d1b5f412abb1db0889831bdb83e02f72d224b0a936378ffea50.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 21 2, .triangle 24 1, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint eb375add48312136919629059266b1d51666d1ef2830d2376129df6d04f34bac.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![0, -1, 0, -1, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint eb39b2d641f5e7b1602ca5addb571032a46536818bef9f9fc0923640980bffa4.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .gapLower 4 3, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Cycle fingerprint ecb428a58f9bb01b0413aefc0702e47d9da31586ef066cd3339b52f10ff4b236.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-1, 0, -1, 3, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 20 0, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .gapLower 6 2, .triangle 21 0]

-- Cycle fingerprint f0e519ed57ac00af92d63a39c946269079fb2dc4b7aeb27816235179feb99856.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint f4d3632d7a8380e90eecc353d6e2c4b20d46e31d24423f84be8b9d3b596d4890.
def localCycle00160 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 1 0, .triangle 21 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint f58bb0ddbd73196bfa8c146431299619aa46e9f96d0f485388415e5007f365c6.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00162 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

def library : Library := fun id => if id < 81 then (if id < 40 then (if id < 20 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))))) else (if id < 30 then (if id < 25 then (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))))) else (if id < 35 then (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))))))) else (if id < 60 then (if id < 50 then (if id < 45 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))) else (if id < 55 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))))) else (if id < 70 then (if id < 65 then (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))))) else (if id < 75 then (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))))))) else (if id < 122 then (if id < 101 then (if id < 91 then (if id < 86 then (if id < 83 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))))) else (if id < 96 then (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))))) else (if id < 111 then (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))))) else (if id < 116 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))) else (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))))))) else (if id < 142 then (if id < 132 then (if id < 127 then (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))))) else (if id < 137 then (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))))) else (if id < 152 then (if id < 147 then (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))))) else (if id < 157 then (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)))) else (if id < 160 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 0, 6, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 76 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18560)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 1, 0, 6, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 19 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18561)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 106 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18562)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 106 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18563)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 5, 2, 6], ![3, 1, 0, 4, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 106 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18564)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 106 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18565)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 1, 6, 0, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 88 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18566)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 111 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18567)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .tail 41 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18568)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 5, 6, 2], ![3, 1, 0, 4, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 100 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18569)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 39 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18570)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 48 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18571)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 145 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18572)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 4], ![1, 3, 0, 5, 4, 2]], proof := .tail 130 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18573)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 5, 6, 2], ![3, 1, 0, 4, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 76 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18574)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 4, 2], ![1, 3, 0, 5, 4, 2]], proof := .tail 72 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18575)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 92 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18576)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 45 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18577)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 120 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18578)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 38 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18579)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 6, 2, 5], ![3, 1, 6, 0, 2, 4], ![1, 3, 5, 0, 4, 2]], proof := .tail 130 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18580)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 0, 6, 5, 2], ![3, 1, 6, 0, 4, 2], ![1, 3, 5, 0, 4, 2]], proof := .tail 26 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18581)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 27 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18582)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 14 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18583)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 119 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18584)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 76 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18585)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 45 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18586)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 133 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18587)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 4], ![1, 3, 5, 4, 0, 2]], proof := .tail 117 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18588)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 6, 0, 5, 2], ![3, 1, 6, 0, 4, 2], ![1, 3, 5, 4, 0, 2]], proof := .tail 131 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18589)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 53 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18590)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 1, 6, 5, 0, 2], ![3, 1, 6, 4, 0, 2], ![1, 3, 5, 4, 0, 2]], proof := .tail 158 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18591)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 6, 0, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 44 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18592)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 1, 6, 0, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 60 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18593)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 4, 6], ![3, 1, 0, 2, 4, 5]], proof := .low (![59, 36, 12, 22, 78, 25, 127, 71, 23, 101, 89, 137, 32, 50, 49, 57, 105, 155, 8, 5, 10, 34, 104, 54, 102, 37, 107, 1]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18594)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 4], ![3, 1, 0, 2, 5, 4]], proof := .low (![61, 36, 135, 22, 78, 25, 127, 71, 23, 101, 89, 125, 32, 50, 49, 57, 105, 155, 8, 5, 10, 121, 104, 54, 102, 37, 107, 1]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18595)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 0, 6, 2, 4], ![3, 1, 0, 5, 2, 4]], proof := .low (![31, 36, 135, 22, 78, 25, 127, 71, 23, 101, 89, 94, 32, 50, 49, 57, 105, 155, 8, 5, 10, 121, 104, 54, 102, 37, 107, 1]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18596)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 6, 0, 2, 4], ![3, 1, 5, 0, 2, 4]], proof := .low (![82, 68, 147, 58, 78, 25, 52, 16, 97, 115, 89, 30, 86, 0, 141, 57, 62, 28, 123, 5, 17, 13, 104, 54, 136, 37, 107, 1]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18597)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 2, 6, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 1, 0, 2, 4]], proof := .tail 126 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18598)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 4, 6, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 1, 0, 2, 6, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 7 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18599)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 4], ![3, 1, 0, 5, 4, 2]], proof := .tail 162 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18600)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 6, 2, 5], ![3, 1, 6, 0, 2, 4], ![3, 1, 5, 0, 4, 2]], proof := .tail 162 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18601)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 6, 2, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 1, 0, 4, 2]], proof := .tail 126 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18602)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 1, 0, 6, 2, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 20 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18603)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 4], ![3, 1, 5, 4, 0, 2]], proof := .tail 162 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18604)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 6, 0, 2, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 1, 4, 0, 2]], proof := .tail 126 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18605)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 1, 6, 0, 2, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 139 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18606)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 4], ![3, 5, 4, 1, 0, 2]], proof := .tail 81 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18607)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 42 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18608)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 4, 5, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 132 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18609)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 5, 2, 6], ![3, 1, 0, 4, 2, 6], ![3, 1, 0, 2, 4, 5]], proof := .low (![128, 36, 12, 22, 78, 25, 127, 71, 23, 101, 89, 84, 32, 50, 49, 57, 116, 155, 8, 5, 10, 34, 104, 54, 102, 37, 107, 1]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18610)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 5, 6, 2], ![3, 1, 0, 4, 2, 6], ![3, 1, 0, 4, 2, 5]], proof := .low (![31, 36, 12, 22, 78, 25, 127, 71, 23, 101, 89, 2, 32, 50, 49, 57, 105, 155, 8, 5, 10, 34, 104, 54, 102, 37, 107, 1]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18611)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 5, 6, 2], ![3, 1, 0, 4, 6, 2], ![3, 1, 0, 4, 5, 2]], proof := .tail 76 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18612)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 4, 2], ![3, 1, 0, 5, 4, 2]], proof := .tail 140 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18613)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 6, 5, 2], ![3, 1, 6, 0, 4, 2], ![3, 1, 5, 0, 4, 2]], proof := .tail 140 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18614)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 0, 6, 5, 2], ![3, 6, 1, 0, 4, 2], ![3, 5, 1, 0, 4, 2]], proof := .tail 126 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18615)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 1, 0, 2], ![3, 1, 0, 6, 5, 2], ![6, 3, 1, 0, 4, 2], ![5, 3, 1, 0, 4, 2]], proof := .tail 7 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18616)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 6, 0, 5, 2], ![3, 1, 6, 0, 4, 2], ![3, 1, 5, 4, 0, 2]], proof := .tail 153 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18617)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 6, 0, 5, 2], ![3, 6, 1, 0, 4, 2], ![3, 5, 1, 4, 0, 2]], proof := .tail 159 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18618)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 1, 0, 2], ![3, 1, 6, 0, 5, 2], ![6, 3, 1, 0, 4, 2], ![5, 3, 1, 4, 0, 2]], proof := .tail 153 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18619)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 1, 0, 5, 2], ![3, 6, 1, 0, 4, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 153 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18620)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 1, 0, 5, 2], ![6, 3, 1, 0, 4, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 153 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18621)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 1, 0, 5, 2], ![6, 3, 1, 0, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 83 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18622)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 0, 2, 6], ![3, 1, 0, 2, 4, 5]], proof := .low (![91, 161, 64, 22, 78, 25, 154, 63, 149, 160, 89, 9, 129, 46, 49, 57, 69, 79, 8, 5, 10, 24, 104, 54, 70, 37, 107, 1]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18623)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 0, 2, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 39 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18624)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 0, 6, 2], ![3, 1, 0, 4, 5, 2]], proof := .tail 92 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18625)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 0, 2, 6], ![3, 1, 4, 0, 2, 5]], proof := .low (![152, 156, 64, 74, 78, 25, 112, 51, 11, 18, 89, 75, 96, 114, 29, 57, 99, 109, 124, 5, 10, 87, 104, 54, 146, 37, 107, 1]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18626)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 0, 6, 2], ![3, 1, 4, 0, 5, 2]], proof := .tail 76 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18627)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 6, 0, 2], ![3, 1, 4, 5, 0, 2]], proof := .tail 53 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18628)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 5, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 6, 5, 0, 2], ![3, 1, 6, 4, 0, 2], ![3, 1, 5, 4, 0, 2]], proof := .tail 77 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18629)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 1, 6, 5, 0, 2], ![3, 6, 1, 4, 0, 2], ![3, 5, 1, 4, 0, 2]], proof := .tail 80 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18630)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 6, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 1, 0, 2], ![3, 1, 6, 5, 0, 2], ![6, 3, 1, 4, 0, 2], ![5, 3, 1, 4, 0, 2]], proof := .tail 7 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18631)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 1, 5, 0, 2], ![3, 6, 1, 4, 0, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 122 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18632)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 1, 5, 0, 2], ![6, 3, 1, 4, 0, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 122 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18633)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 4, 5, 3, 0], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 1, 5, 0, 2], ![6, 3, 1, 4, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 143 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18634)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 118 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18635)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 2, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 56 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18636)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 6, 2], ![3, 1, 0, 4, 5, 2]], proof := .tail 76 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18637)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 0, 2, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 14 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18638)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 0, 6, 2], ![3, 1, 4, 0, 5, 2]], proof := .tail 45 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18639)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 6, 0, 2], ![3, 1, 4, 5, 0, 2]], proof := .tail 98 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18640)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 90 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18641)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 0, 6, 2], ![3, 4, 1, 0, 5, 2]], proof := .tail 76 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18642)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 6, 0, 2], ![3, 4, 1, 5, 0, 2]], proof := .tail 85 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18643)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 6, 1, 0, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 108 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18644)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 1, 0, 2], ![3, 6, 5, 1, 0, 2], ![3, 6, 4, 1, 0, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 103 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18645)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 1, 0, 2], ![3, 6, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 21 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18646)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 1, 0, 2], ![6, 3, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 35 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18647)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 5, 4, 6, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 113 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18648)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 144 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18649)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![3, 1, 0, 4, 5, 2]], proof := .tail 19 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18650)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 0, 2, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 134 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18651)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 0, 6, 2], ![3, 1, 4, 0, 5, 2]], proof := .tail 110 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18652)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 4, 6, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 6, 0, 2], ![3, 1, 4, 5, 0, 2]], proof := .tail 6 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18653)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 65 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18654)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 0, 6, 2], ![3, 4, 1, 0, 5, 2]], proof := .tail 19 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18655)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 6, 0, 2], ![3, 4, 1, 5, 0, 2]], proof := .tail 6 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18656)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 1, 0, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 67 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18657)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 5, 6, 4, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 95 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18658)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 95 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18659)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 5, 6, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 95 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18660)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 1, 0, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 33 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18661)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 1, 0, 2], ![5, 6, 3, 1, 0, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 40 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18662)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 5, 4, 3, 0], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 1, 0, 2], ![6, 5, 3, 1, 0, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 15 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18663)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 66 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18664)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![1, 6, 0, 2, 4, 3], ![1, 5, 4, 3, 2, 0]], proof := .tail 43 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18665)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 2, 3], ![1, 5, 4, 3, 2, 0]], proof := .tail 93 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18666)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 2, 3], ![1, 4, 5, 3, 2, 0]], proof := .tail 150 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18667)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 2, 3], ![1, 5, 4, 3, 2, 0]], proof := .tail 43 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18668)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 0, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![1, 4, 5, 3, 2, 0]], proof := .tail 3 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18669)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 0, 5, 2, 3], ![1, 6, 0, 4, 3, 2], ![1, 5, 4, 3, 2, 0]], proof := .tail 157 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18670)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 0, 3, 2], ![1, 4, 5, 3, 2, 0]], proof := .tail 151 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18671)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 0, 3, 2], ![1, 5, 4, 3, 2, 0]], proof := .tail 4 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18672)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 0, 3, 2], ![1, 4, 5, 3, 2, 0]], proof := .tail 151 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18673)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 2, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 3, 6, 0, 2], ![1, 4, 3, 5, 2, 0]], proof := .tail 55 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18674)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 2, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![1, 5, 6, 0, 2, 3], ![1, 4, 6, 3, 0, 2], ![1, 4, 5, 3, 2, 0]], proof := .tail 142 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18675)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 2, 5, 3, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![1, 6, 5, 0, 2, 3], ![1, 6, 4, 3, 0, 2], ![1, 5, 4, 3, 2, 0]], proof := .tail 138 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18676)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 2, 5, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 5, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 3, 6, 0, 2], ![1, 4, 3, 5, 2, 0]], proof := .tail 47 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18677)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 2, 5, 3, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 3, 0, 2], ![1, 4, 5, 3, 2, 0]], proof := .tail 142 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18678)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 2, 5, 3, 4, 1], ![2, 5, 3, 4, 6, 0], ![1, 6, 0, 5, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 1, 6, 0, 2], ![1, 4, 3, 5, 2, 0]], proof := .tail 73 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18679)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 66 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18680)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 1, 0, 2, 4, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 43 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18681)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 0, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 2, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 93 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18682)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 2, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 0, 5, 2, 3], ![6, 1, 0, 4, 3, 2], ![5, 1, 4, 3, 2, 0]], proof := .tail 157 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18683)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 0, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 2, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 43 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18684)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 2, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 0, 3, 2], ![5, 1, 4, 3, 2, 0]], proof := .tail 4 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18685)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 2, 5, 3, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 0, 5, 3, 4], ![1, 6, 5, 0, 2, 4], ![1, 6, 5, 0, 2, 3], ![6, 1, 4, 3, 0, 2], ![5, 1, 4, 3, 2, 0]], proof := .tail 148 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18686)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 2, 3, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 0, 3, 5, 4], ![1, 6, 0, 2, 5, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 0, 2, 3], ![4, 1, 5, 3, 2, 0]], proof := .tail 150 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18687)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (18560 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 18560 ≤ id.val) (hhigh : id.val < 18688) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 18560)) = true := by
  let j : Fin 128 := ⟨id.val - 18560, by omega⟩
  have hsum : 18560 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (18560 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard145
