import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard085
open N4R2OuterLeftReplay

-- Cycle fingerprint 01be598380c04f413c9e48b9f0d3d648066bb661a1c802f10363153ff599d0a3.
def localCycle00000 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 01d0acc7ca822b340390ab5e795d6a28fd8eabe26815a880827426bf61e9b55c.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 01e13a2c6a15e2c0fcf767b6608f6e220debaae2292dcd14c1bc5bf283283eb9.
def localCycle00002 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, -1, -3, -1, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 0, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 02661c9e5fff843f89cb77ce13310dc2c6cbc9e248741f8d7219caf9f796b572.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 02c7e4e5e2dc82da1c4aaeed7bf1e1d2c8cb0c9f6b612f2a7ff2099aa2eb369c.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![-2, 0, 0, -1, 0, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint 03e6221c2aab753764e1619b903ecb7c4bd5457d7312709b92799c527cca6c07.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![0, 0, -2, 0, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 3 0]

-- Cycle fingerprint 04eb638132b2d195530b8a47b793b8bcb8dbd2ef5d2907dc10a1da00374aa1f4.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 063ac42b25120f944d507c678fc9c9cee5bb7cb23deea55dde9fbe8409e4daba.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .triangle 15 1]

-- Cycle fingerprint 075997d6f258237cb788c5b1d4e629e17a29f5e824ce58b0a99ad1b5f21d4e9a.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 07aa28fafa36b9dd2df48ed3039771cb855683ffa90d71d1e568182391bc895b.
def localCycle00009 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 094b99e73afe18e235b60308c4ae4fdc8db00e5815ac06646b39e72b2b63921a.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint 0973b7b0f60e4633f94db3acf0282405aaa37196fd505b1c722354a800eaef30.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .triangle 25 1]

-- Cycle fingerprint 0997d2c22d53de0fea3fab3d1b3a79bfda02464a147d43840805e2e9024456f4.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 0d440bd9e6f5b608d1ceef2e04d8b803f009b51b72d626f63980926b2c1e0a68.
def localCycle00013 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 0dbd934737d86fdc76a812aeab35606d46f45eff23074d037c07182decfd39d4.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 24 2, .triangle 23 1, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 0f8ebe56f0ef7bb578f1ee5b4ffc3d5f10f66e7bb0c9465d3df6b346eeead18a.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 11092a48c09279488a981da64d9ece8790e41e36f8ff2fb59ee470ee1e88129c.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint 1350a5b1c54f1f74c446f090972c0a6bd60e4134037e5f1ca6d93a832720fa44.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 138785cb4422698531f1b027bdd208788bfd6926dbefdc989129d335ae9f96fb.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 2 0]

-- Cycle fingerprint 13ea17a5a22ed2cbe0f256459a820377794a61d7cf32ed6fecb0d1d41b3b9a9e.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 1, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 181a68137934dc952d4a7ec9cf15c492e5330697f0a57794526beda7cec400b1.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2]

-- Cycle fingerprint 18471900e87a1294d1077a9c04a8dfb700ec8b43f652e9b8f93c88d7d4820362.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 187507e0dbf35a871c2defb15649607c109a09f87dc136bbf11b88c786a0fb81.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, true] }
  origin := ![.triangle 2 2, .gapUpper 4 3, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 0 1]

-- Cycle fingerprint 18c1c247e6a2329e4af0bcc4e786a8fa7c25a07c2654a4b427c25e32458d2104.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 4]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 2 0]

-- Cycle fingerprint 1a11c966160b8f90b5cfabdcc413db697107488231d2b5dcc6ab54f31e0598c0.
def localCycle00024 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 1c0bb1931406235ebbebc4310da1faf95deb39780770233a9c9730e765dc21a7.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 1c5579eb5bb8400f22e3fc3330e30ec78a4e7ef3c963b5aac4c4de4bbe98f782.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, 0, -1, -1, -1, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 1ca3ce98341f7eec80865dc4a1648459203df0beaa9fa0460eada0899147991d.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 1d6a79e57c51273b8ff42e859234251bf5f634f61aab0666cc12d4d631980e33.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 4 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 1e31d54efb42ac37d9b069dba4d3cff22eebc8c79c3a364fe62c39e856dfaa12.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -2, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 216298b081cbe96ee33c2dc0d1d629342753ad9b5c3c083d10f1447ecdf9fb72.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 22132501552c37ce7385ab8653d05fc042e5c7c00505fd7e53671dac1aabaa50.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 2290e91300ed652d2746f96c4499741cd2cf422945c230e4d461fcceb7c6c453.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 0, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .gapLower 2 6, .triangle 17 0]

-- Cycle fingerprint 231a97baadf1c3a73af67e67c7935d4c6cd1c756f7d3cacec2042efc8b726e56.
def localCycle00033 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 24ad2302af720c898689c2d59b584f8cdae5b5db465d18528fe29f3793a1d881.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 0, 0, 3, -1, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 19 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 2584d94b500a945fffc4176eb92dd524e5ae1ed72d09f3a7b278411e7085a1fa.
def localCycle00035 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, -1, -2, -1, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 25a772692ec050ad3e22f1410109e117cb6d0e1ae42ed123ee615fa8fa087ce6.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0]

-- Cycle fingerprint 25fe51eea54b946c9b58be7886565f244fc6e5cbce6eaf566bccb81062a05ce7.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0]

-- Cycle fingerprint 2754f27f84f5235d3b6949d33b15a337fbf2f9418ffbd105c69d68bf08974333.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 2a3139efbbaf9578a4cc1909cdcf25e399e31964699fedeb238ebe9632e025a3.
def localCycle00039 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, -1, -2, -1, 0, 0, -2, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 0, .gapLower 1 4, .triangle 3 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 2a422ddfdfe64ac06dfb91452b2a6b42a9947b305cf96035d838f50194325a72.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 4 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 2a71e382fee7aa96d8c8fef084b1dab8c42ef2dfd59faaca09e5f9d79a792700.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 2a981581746d0782db53b07b9b8caf213714ced7a2570391c405fd1fb53da051.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3]
    constant := ![-1, 4, -1, 0, -3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 2 3, .gapLower 2 6, .triangle 18 0, .triangle 17 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1]

-- Cycle fingerprint 2c620bfe307a0cd89da4eef6685f6c4ba33dcb188d121ef80e70f5228aa62e8c.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, -1, -1, -1, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 2cbf9f4ae8dcfc71c778f9e645c0298fed8d54ebae9a318e51e1f4ed90abb432.
def localCycle00044 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -3, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 2d37286233950c8806e9ab3d2d8a6701cd1c6f32a7976390fde26e5c49500dcc.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 16 1]

-- Cycle fingerprint 2e00c41e1f7a853edeb267df273d64a815b76970f0c39bdd55a6c456efe550d4.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 2f1eb204d61eab74e5568ed7d06dffe910aaf6951ecafb0230de3840070ac515.
def localCycle00047 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -2, -1, 0, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 2f4b78a565dec3213fa495fd188fe4a4966554e0e2f378c146b9334ef580d755.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, 0, -3, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1]

-- Cycle fingerprint 312be849cdbd05e2121c8c957c6bd3beac9f84b20ec096cb0409a2de33f74668.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Cycle fingerprint 3200dae7716921512c87deb942a9080deea1e9a930ad21e92d3e1a2b51ada9cd.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 329495e67ad5058bf8d9fbad8419522a5beaf48e39266d8d9a2d6c02c84f42fd.
def localCycle00051 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 3364a3004d5b2914286df4cdb174f6a73c77ab1bce6a8a7aca63046f3c79ea04.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 33688cc20e42a4f21f4de2ecfddcad331490b98504112b27d5557e60ade5ff35.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 34ca2aee228f3ed04bfcffe5b6b2e7631ccf6b603acc6f048d0fd9a02cf253b1.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint 3917c800ebd6959c8a77323d2fd50de3d348f943dffedec4cbe4e369d1de0c11.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 7 2, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 39601df57681941884db4fb6a895dfa18624d16bf600ae6cfe2aa2257e21b00c.
def localCycle00056 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 17 1, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 3cc9f8e9d8627ac94f48bf0483ab5a8d224262cd4cba6d0c0e5a4ed71d61f344.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, -1, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 3d5fa3d084bca24e390dd7a57239af626e19fb151bbca262d72c686905b379cc.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 2 6]
    constant := ![0, -2, -2, -1, -1, 0, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 6 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 3faf4af3d6c6c1b43e03d94ad1d1907a88b9bbda99acea3e28f0b83ce5c92b13.
def localCycle00059 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 428ed320adbbcba04bc9a45515cc53276ba9e90880db138e6252b4646b44ae33.
def localCycle00060 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint 42bbeb1db94777af13981fff8cb1b6410923460bc695f0fdbba3c02baadfd05e.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 43058db3028df0a54149b672700ae2ab876f61684d9cce549dfe2f88d582f532.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![-2, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 18 1, .triangle 27 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 4397d7b73636a8fea98aff903b74f9633f9d2f503567fbb1b14e811f25c191c7.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .corridorLower 2 5]

-- Cycle fingerprint 4410501bbd5140e4f770c59f921db96b361c71ac60ef841440fcae9795121f07.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -2, -2, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 45356d02522b0c185d7a967a3c8056b3af34d24a1a3dec3f8354a435fa77f16d.
def localCycle00065 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, -1, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 5, .triangle 17 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2]

-- Cycle fingerprint 460fa16ffe41135419768b27489d539e7558fb19c8d85a0c4f0ef71830d485cf.
def localCycle00066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 473e8a9fcab03725f8be50018c45dcfe1535d2e1684df32af37e0716de412a08.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 0 0, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 47a91fa0f63109d2ee1258fc1cfc7d02db56a1a59aa328eaf4006e26cc64aef7.
def localCycle00068 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -2, -1, -2, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 4e7f2db5e692bbe86a658758237c3d88678cdda63dae2880ea647d84c6343afb.
def localCycle00069 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 5035f4b0cf895f633fca87e598bf1897925e76b469dbb0ad49b2cc6c97a29441.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 50a0bb902577cb03e4d29ea5270e3ca2e209887448466d08ff90573481159a54.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 51d13c0867b2229a8ea7fab632f1d44da51bdad51ba4a61b70ab94b5ecc99bfc.
def localCycle00072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint 52e75df622ca15618b4b85e333d749c363bbd74018e611246977aaed871922b1.
def localCycle00073 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 54f7274a3789cde50f4363450310a0cb376993d780eb20a0b12a625a24f57d06.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 552ece98618f6552c2c57fb2cf9e5e3a32da48d7a67b2dda7d37103a92d141c1.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -1, -1, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 55e744adf237a8c63925f2a05d4b55cf44e0efbf3fc48679a983411c7ae60bef.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 23 1, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

-- Cycle fingerprint 57397002e879b01efd2bf05a4b4801127b5dd0802743a9de176e5f52767b6a91.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2]
    constant := ![3, -2, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 3 0, .triangle 4 0, .triangle 23 1, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2]

-- Cycle fingerprint 57b2d28ee4606cf4fa29a0748a2b4af8dbedc66b4f2fb94e48f66d5594b8c046.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 1 0, .triangle 15 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 59299489460a06638acbe72d5360eefd1d6e580d0280ce67f35d3117ff5a2743.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, 0, -1, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 5981025da62d104b3caee5532a2d79e8bc75ad332a9f0201db7abc464701ae99.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 17 1, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint 5a2908e2a50d60d199d9b67127961d044d0bb9daa62d8af6d3b4a395b8245017.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 5bf9d038c6e5138a86a155c0a833bada11633d2d8a0bd60fa8a91f54efebc6ab.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4]
    constant := ![0, -2, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 5c0893346c3373a6ef5cff81371b505becb9e6427a59c29d74fbc76890d67d53.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint 5f4e4bc3618ec52536d2ef1d60cf27274d777dc6a70d0bd575c46abd11a65bad.
def localCycle00084 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6031472771ae8fb1fd03beb411b73415164627d1f030d15872aebae2b719df0e.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 23 1, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 603d8c1ff48105a181fd1f190cf6671cedda5575be64a95c0f8a8cceb127146c.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1]
    constant := ![0, 0, 2, 0, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, true, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0]

-- Cycle fingerprint 6060c757dd8756855c7ed1f8157ccdc2330ddde6829d74d3eb9c41ee828fdce2.
def localCycle00087 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 606f80c6986522f11386f83a10c460605436274a27d8ac0f80485c921dc12df0.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 60ba51ed009eba4058a289f9e42813e13f1d814ffe828a40495e6097324c0d96.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1]

-- Cycle fingerprint 63132182908530899e9b75e38f1991e1b2fba53c61fd68ccae9adadab3d78a14.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, -1, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 6353bc83921575a883e0d2842b40a12b00d1422640bff15eb5295ebee7b83d4f.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![-1, -1, -1, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 66f8c406b967269c233450af9e01e9082981839c4df6da10d8c4918026184ecb.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, -2, -1, -1, 0, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 68912662b39836e2fd00c0f4407f31e8a0cdb812ad822b99f06eee10c72a928f.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 6a14f77036f2cd9f9d986c5befd8a5904795b7edf1fd889babcd08bcb2d1d4d9.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 6aa121cfd955047e990d0dad609a41c7757e45f9fa61e230d9ddbfe5cb7f5d51.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3]
    constant := ![-1, 4, -1, 0, -3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 2 3, .gapLower 2 6, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1]

-- Cycle fingerprint 6ae22b33d0b3e7b4153353162083857065a7d0e5c80ce69ae81619dc45c2ae54.
def localCycle00096 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 6bfdb8f933f9875515fff9186d4d05141615f7b983d14f088ea13c00cf79d39b.
def localCycle00097 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6]
    constant := ![-1, 0, -2, -1, -2, -1, 0, 0, 0, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, true, true, true] }
  origin := ![.triangle 18 0, .triangle 17 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2]

-- Cycle fingerprint 6c970117d6bcb078603e055ccb4f51b466ed493b21b0ed13686d11738d8823be.
def localCycle00098 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint 6db1e636705c67925d63bcd88986bd10ea56db7da475e498569e2cf55f96626f.
def localCycle00099 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint 6ead6f0db22f2eaa4cfc60b8731ecfd05778e2c5b88bd5e9b9bed26fca034bb6.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 2, .triangle 17 1, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 7218e55e774dde8aa69b6803acb7a80033f7c33a798bf52a81a98de9e8d1edd4.
def localCycle00101 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 723f20427d0a1a2531efef885982f0d361533d483566a1b2593b2d571f799074.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 16 1]

-- Cycle fingerprint 72bbc71ae509797672df8458f5662fd8b0c29b57c102324972e774a5c33d499a.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -1, -1, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 2 0, .gapLower 1 1, .triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 73b1eb5dcbeec24082797231a14b4f098eb4e15f716d274ec23874aa5b96fa55.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 755197db747fd76b4a55e5344c12823ca418d3decd74d38b5e742bffbbeacded.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, -1, -1, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 76898fb01e51d226b7356ab68324a28645f2e366b40ab4742f203cc84725043f.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint 76d47b7ca7fba883b621b052f23554328fcdc41e8a83499bb96133383050f6ec.
def localCycle00107 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00108 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 78491dfad108f8835463061ae89d207c0580c5118a44f3915256622c49707fa9.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![0, -1, 3, 0, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .triangle 23 1, .gapLower 1 1]

-- Cycle fingerprint 78b5fe9adedc85c1ec152f7223a13e02d7b36336d679cc770b3a2ace1b211df3.
def localCycle00110 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, -2, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 7930ccdce91d4bc49242d2751054948b23040f6d7b22105463253883bc3b1567.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 4]
    constant := ![0, -1, 3, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .triangle 18 1, .triangle 29 1]

-- Cycle fingerprint 795a7905646e7d0eebe61d3318af63e5b936dfb42cf8e274ea2148e19cbc3fd1.
def localCycle00112 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 79db4109288f7e49a065c295394a5b868799588625bfa133dc05f84e68d86e69.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 7a768884402593750c97454535272ed8adeef10489e82fbe12d0f1acacb0a2a5.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .gapLower 4 5, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 0]

-- Cycle fingerprint 7db05c32141b189374babbe68998f3ad08e3e46795f9ef90f0804273ac558339.
def localCycle00115 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 4 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 7e256c748ceb52a0fd206841a4e2146e13c9e17a37bb4044766830bf4a332a74.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 7f33b825fa4034da8ca5aa4e6b69e447436256ed636e2d7acc3d2c6f62caf755.
def localCycle00117 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 7f71a21734afcf5308d4646abb219f7d5c8e9bc7d3081faac1967eb7563c3cbe.
def localCycle00118 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 7f7c9f4b904294c1f5a0593432424a4f36a7afc58474b77c23fcd07797a14b72.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 8092c67f6eeafdfa484e6dfea097af3abc5be60ceb2c202c21cac21416cadc13.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 8100d989361e5259a600505a1509cfe27f895ebc2f91284a4932710a6d338ddf.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .triangle 8 0, .triangle 7 0, .gapLower 5 0]

-- Cycle fingerprint 819a42901b0af107dba48a1c8d03a8f32c91106c68ff77202eda08375b40acb5.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 8383fae31af2a4416efa0885fac3f08df01f52637d74bf972a6ae17c72d10966.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .gapLower 1 3, .triangle 23 1, .triangle 19 1, .gapLower 1 0]

-- Cycle fingerprint 83896cc6629835a0d210968bf1e22cd0390aefb3f247cbe3fd4aa598193dbe6d.
def localCycle00124 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 83d38e5f8c094a567f76c0cd566c5d1aa527db880bf7019116fa95d57f235b8a.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -1, -1, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00126 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 865d69eda704dba5cf2ec6933a460d02ba329d1ed5d8d442dd849116d73c8cfe.
def localCycle00127 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 8a75c3c2e12509ae0fc0d56701726ac3ac1fa2fdc36c92d1877135a4a10cb031.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 8aea7680037d7c9cad508e6265d4301d2947fa1361669e4b3800e8349ee1e024.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 8b036b3c8dba6c88845e864d00a41a2f38d1dede6ef22dbce7ebd15ba50394c6.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint 8ba05de0cacb76b50e797a81d924d43c978d920942b52921bba3e9be91796982.
def localCycle00131 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint 8c4f861e1dd60552710d3a4d3327a87058514c4850050377a4177464b8f36776.
def localCycle00132 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 8de6bcf23e6d2898af15dc84b3b1cf43e66a1c3b55e554a5802267f16d012358.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -2, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .triangle 19 1, .gapLower 1 0]

-- Cycle fingerprint 8e6dec607b68c6b8024206f82227405be540acbbf4683c4a8ef9bd3efc51d9f2.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Cycle fingerprint 8f56e3a8fb598a13919085121839dc7c62b3e318a27d0ca9ee08e97f24a92227.
def localCycle00135 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9088b7528948f8b75cbc41e993ce7a86d359bb53d9508f885b0e83c619b8168e.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 90f7e837a5617332fb181a04c3d77baf5f73d8bb748ce14002dac371dd7b092a.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Cycle fingerprint 92dcaaed3f8d9042c38324116b918baff27e0edc62ae833cd898596d677d0699.
def localCycle00138 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 93b2a005e71dc1ef76e9956c3a1c92406ece20fc40b278c5dd4f5971906e6e53.
def localCycle00139 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 956b517fd9f611f2602b3492b98132be558f65919e3954df1c1d604ecd6592bf.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 95859e224df2cd644965a93e8ad38bed6ee0845b67e1f4e197f186efbd9f7884.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 965460dc1a5548fb6eac65687c4f36cc719c9024436e1bbbb9bd0eab81d892b2.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![0, -2, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 99a4b437a3a694189e9da2aff5ab30cd04d056271fba69e45ab0f6e3fa7a8937.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 9b5346fd3399cf5b0255572e259321b3b0075fdf0a6fb5d88ee03675763e0e0b.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 2, .triangle 9 1, .triangle 11 0, .triangle 21 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint 9c0ef2c863231a9244f1bbddc570d4de3fadf012cbf6a188d6b7e06f1029e0ec.
def localCycle00146 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9c75cf303434220b37b4733fb35744a144e4b1d1e3e79882a60b65b4aec7c5a3.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .corridorLower 5 6]

-- Cycle fingerprint 9c787cc7a8a1b2445e1de9b4887a4faf2c5005f0532ba95812a4d446cd8a1ffc.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9d0b4886c23e795e8abbc1a97880a71a298533f4697a5f2af7c986bdf7f257ae.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 9e8783bcd52af3f94f3a1d04ffe26f50c5ca2881d92d5ca12b98969045059155.
def localCycle00150 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 9f9bc6aae47342e51a842ec63794e2a8d69e6188782814e0f86765c7ee244cf2.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 2 0]

-- Cycle fingerprint a10a487d5943d2381a00492b5bca1f41ae7b57ea0abf0ccba83fecf92b6639ab.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 0, .triangle 2 0]

-- Cycle fingerprint a1554412fa41108464db70aff92bae12815e24c13d9963012495523a531a6fb5.
def localCycle00153 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint a17ccf9f1b1968eb43782d31f46e447b4300596e301880813e74e823120e7616.
def localCycle00154 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 20 2, .triangle 24 0, .triangle 30 0, .corridorLower 2 5]

-- Cycle fingerprint a348717264173691f6bf1fec96754d93d1dd4a44f34c3705118b1c678648e8b0.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint a3654eeaa0ac0dee4e55dba74470ee705cbe7ca11a2b53eba99788907e6e8a20.
def localCycle00156 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 2, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint a3dbd89fd0ed89b7031798f4f1655d35ab3ded06a9750d9bc1e591dd687cdaaa.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .gapLower 3 0]

-- Cycle fingerprint a412a9c154ab0d1247370e631362e8676d2a4fe41fc549d15c3676960351df0b.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint a4c2388fab2e66b8d12b4eabf36c315cd18a978522ed35e6e2ce5e62a8412e50.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

-- Cycle fingerprint a50a6f0fda26874b2f124b47819ab5af5dcf9f74034a12f5f776f2f0fc070274.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint a55e6d077f3fe932e39f04bbf1785fd13e1e7ac1f941c6128d9b08ca48587b01.
def localCycle00161 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a5a94d4ab26ff257cad1c3476a47316f91bb75862295dda658863a39677db40f.
def localCycle00162 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -2, -1, 0, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint a5af5fba1eef55ed5fcb2f2ee620c7d1e3ae049a0878a8c223e1cd8732e11c3a.
def localCycle00163 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .triangle 19 1, .gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint a7e8736f7bc2f617d75b37add34c96b6f4fba001cb1e4b1869235f2f0f993ef9.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint a874314bc34bd720492602d4a01bcec70a62f246fc5657622aa61301072a4ce2.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 3, -2, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .triangle 2 0]

-- Cycle fingerprint a8c25fdb0eb9df7a8401eabf1998c4d88ef2425db2672d75b4433c64894ec924.
def localCycle00166 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 24 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint aa58dca5d604df6347fcd4168470f39010168e2ea87a1cf699f7476eec48f801.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint aae2d3f5250c3cb5b71668c9b45e2d12240a0a4c468d97b7241b8454c6cf1041.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint ac53999ad082aaa1e374c8f87bc31c5d5f4d938b1ba11e2ca58ca11ccbb86849.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .gapLower 1 4, .triangle 3 0, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint af46d9abb60cbcfb734a1a9894a854f35304139f5f947ee44282279671436781.
def localCycle00170 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 24 1]

-- Cycle fingerprint afef2154edbb50a9ab945a07acc5b3a2c9b476b87ba7e2803ccb3d8830915015.
def localCycle00171 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b0b4385736d6ee03301c8238f4b939801fee2a3dcddf1961b96d732bcc4046bc.
def localCycle00172 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b13874d59915d3e162651e9682dd7a92d8f361f92af608b5bb420c714bfaa034.
def localCycle00173 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b2a76a8d4e6e9ac7ee5ce6c8e88399e4f4a0c0f438f53f1cc19c223b8cfcb2d5.
def localCycle00174 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b2e5c4f4215192568939e5119614b9639dfd5a21580789e136a19a1cb9337300.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint b46b6b2986d652d378b1e3cc13bdeed5e7d3e3d9422748d15337f0f0f5054dab.
def localCycle00176 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 4 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint b47ae8244ba4d16be10a4a44bc014a584811d4bd986cbccb7f8aac4839afb113.
def localCycle00177 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint b55bf56f6583ebde61b83051921ddaa5c859758133e5f8286540578c5fbccac6.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 2 6]
    constant := ![0, 0, -1, 3, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true] }
  origin := ![.triangle 29 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 18 1]

-- Cycle fingerprint b585e56139a906ee00004ef829313ee2d6edc35824295e39059111451fabb57f.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 30 0, .gapLower 5 0]

-- Cycle fingerprint b591dc266c341a2a870e20dd7ecf734ae7d418f1d8f3252e8ffd9c12bdfaf99a.
def localCycle00180 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint b5cb5f048e1908a3b206919a6f84ee661e0f4943148cc546ae076cf072a95dc0.
def localCycle00181 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 17 1]

-- Cycle fingerprint b7043bb50de9f4d23f099be2915ca9a38b554bf894eb6a55a5f8efda2995a9e0.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, 0, -3, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1]

-- Cycle fingerprint b782f62e243ba6e046fe847f2d1dd09127233e8a94c971a531eb0cf8b2eee4a6.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2]
    constant := ![-2, -1, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6]

-- Cycle fingerprint b7e39d372787611cc0032ba7fb230134e224fe740892c42b3a958c683314a829.
def localCycle00184 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint bb035a09d91bc73981171c42b613370e919ed2305d8fc293ab3991573c4420ad.
def localCycle00185 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint bbbc530694606219bf1de9afe2ef3f675edd0b752d60d6e54b7c62f21d986fca.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 0, .triangle 2 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint c01625c5450490c771b0c1b77360d4f9b1725fe451708e0a09512905ca165ec0.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -1, -1, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c0292796d49597b1705cbf0fd2c81ff3aa5d43a1754670321279e6ffcfe91881.
def localCycle00188 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .triangle 19 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint c0f854e513f32eb2e4be293628d110542fbda8128b1b20914decc9d047ce3ad4.
def localCycle00189 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint c10d3efb5a9d955ce743b2b9814063043ea582e16b634c984d57cce9938aa03e.
def localCycle00190 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c18f5bf2e9b0758bf01dbb672590a1f8c3ea9a7ae7a2065709c84e69594507a0.
def localCycle00191 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -2, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint c1a69647f8a1cde4d8bebb38857d15eefe4c99c34526b1befc883d928dc97682.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint c570c936227dcdc511c2dd63a1136f6e2a4489c228804bae0877208e646eab01.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint c5a8f953766de51f7b46f024b6a9af4fe914dc542eaca102bec16fd37e17bd9e.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

-- Cycle fingerprint c5ecca3d5e34e8d38bcde4c9496a0fe75f5011777587ba5c5ba681e7d839914d.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint c6449293180c6f4b6bd67746ae27321c81e030354949c7d38e38e64cef7ba15c.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 3, -2, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 2 0]

-- Cycle fingerprint c8b1c58ba7a1ab7d8748d0fa7e7d93ce9ec9211e4ba9a72c51829c91b6313435.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c9649a219ef87657a5a32648df49ee22469c0137c9e48ec41c0a950d046e9d6b.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint cb338e99a98ce743f4b0ca8dc05dc976cf5c304674075e37ba9b2bdfbe5d638e.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint cd08368f857d886d96092b38d6ead543cd79929a5b46c48f15634ac8b598a0d3.
def localCycle00200 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint cdcff06dd8a8d5ddf4a7259bacce81ab163dc137679179fdb1aedab6dabd98b6.
def localCycle00201 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, 0, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint cefb692a94a5fe29c25b3fd1578c2ea1b21358120854d0d731cd31bc77431dd3.
def localCycle00202 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 18 1, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint d2dd62ef59112a1fab1c71888bfee0962a239403c4ee2e77c7997071c721f7bc.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 4 0, .triangle 23 1, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint d326422246e2c4d996014b46ed2ba2f064ff56d542c57fb380670478e5cb1978.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 4 0, .triangle 23 1, .triangle 19 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint d36f9c0217ffa14c406644d8d493669e2d9901b1a2adc28010a6ab4262896447.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, -2, -1, -1, 0, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint d3f3860f1a47cd60c358651c048b97c78d8e01a5b2939a6a8773da1e8ed8edf3.
def localCycle00206 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, -1, -2, -2, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint d56801c43f692d67f50dd0a6db354d2efdb20ce56ec20616a8e3d37c89c3c16d.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint d9794d86032070c62af8fd704e2f91ab9494d404281aa470da02a0cf464a1582.
def localCycle00208 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 0, 0, 3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .triangle 2 0]

-- Cycle fingerprint da6e787550d972cd0fd385400e9b04af56caf74e854febaeadb848c55ad8a1c5.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint dc9f351ec4068bb51b5f52e46f9559cb4db60507ef32deb04ee7aedd70f1d5fb.
def localCycle00210 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint dd8109e18aaa3d9364c97c9910e7b7b3dfbf2a506f300aaf767884915c0b078e.
def localCycle00211 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 7 2, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint dda88feb809f9b4797485267c1ecef14e745518aceaae2d7fe220b058e6cd84a.
def localCycle00212 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-3, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint deb65a596b5b535a963b0fb3f193f39ad4ac41c53b707786c0cd81f10ed34927.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -1, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint df455ec88283fc036cbc115cd0b48bb890c9881dd61ad0340b05ffc34cd8f304.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint dfa1f9c7c184e26d3573a8ce0d528de6c9aee25ac45ea8bb1012f3740243d390.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, -1, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint e233165a2c62e7d772a095dae28266b0cff95d56cc8ad2ba39db3a8d88b64b7d.
def localCycle00216 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e29e32c381fd0896c81865cd046083e39d2b76ca7a0e140dc21cb32814156043.
def localCycle00217 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint e3271965c38393f0ca57c425ea828eb78175c906fbacd67ac12c9e74af66ae25.
def localCycle00218 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint e4bcbfab1bfe41b387895506c9e8476c2a3bd73805153a2162a0b6f4b9328447.
def localCycle00219 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 0 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint e562ab20522903d8582587bf4e3a5747163164c4f0bea930a4c9e17a74585203.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint e5dacdc2aec9106a3713aed8417fd7b7200935a625738da271c59b4ba1e3c023.
def localCycle00221 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, -1, 3, -1, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint e73a96d0264e799c60d97823fed0d20ba87719dace0067c1a7228010453cc176.
def localCycle00222 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, -1, -1, -1, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint e93118de1e04beb583df15a9339f1f1a3031fee204c8d556a4ea631fd2989639.
def localCycle00223 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 2, .triangle 3 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint e9901031432102ccbff3830304f348346cb3ca373f75dc3518fa4a6afeec177e.
def localCycle00224 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint e9ca0ced7732f2d4dd9cd84bf9b6b70a6c6bad3da16a60d6a28a0a4dddc3ac89.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 0 1, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 2 0, .triangle 1 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint ea4946a58929ea16bd528d6f2920dd0fefa460249235a26e96a031ffba9aa458.
def localCycle00226 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 0 0, .triangle 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint ec32651dd851f0a36cdca983a53314e454f6984a8d06a8a07e2969753ab8627e.
def localCycle00227 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3]

-- Cycle fingerprint ece0d01ea6066d6c21f1e368e80ba399e73fcd9e2a11714910a54db6855ef2ed.
def localCycle00228 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0]

-- Cycle fingerprint edc06deb69f5cdea1f0ffbdeccd42ca6079f59c5b5d902e627eeb7c89078d3d1.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .gapLower 4 0]

-- Cycle fingerprint ee0362d44e13c53cc75edfad330800e8c598a3cbbd5abc86698557566631acb2.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint efc382b169ee2fa6531973c904ce98de925e2b68e5fefa667eec4d28ba7657fe.
def localCycle00231 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f09043286508c9dfa045a578b9827ba4c7337e1ed04c51e19157ca8ba802bb22.
def localCycle00232 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint f23fd02a50f43470a8c0b6ec7da4d446715bd8e2d0704892c634d45360a9cae2.
def localCycle00233 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 2 2, .gapUpper 4 3, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 0 0]

-- Cycle fingerprint f30279e1b9830b92f799df906e4f0c40a2298d626f64afecc426e66d17f75988.
def localCycle00234 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint f35bbdf29db0505bfbaea45b3729c867c9f2bf591a1ce18c2162c14ed9c7e4f9.
def localCycle00235 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6]
    constant := ![0, 0, -2, -1, -1, -2, -1, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 0 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2]

-- Cycle fingerprint f3fd436dffe1a80619b673d4a116c1b370c1e37e7809ca3fb5a1b233209b7dbf.
def localCycle00236 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -3, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint f44ff366332bf579c16e47b3ba317f3ce8f0dd51ce3992c13da7a341382eb9de.
def localCycle00237 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint f49f9906a0e0b1238ea533e13f7432f8a88b155a7f412dedaec4c918b44cf4f3.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 1, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint f617f7c42d5effa6c3e58ce2c3af4a69c3b6cc5668add27c56c6cc286e7253aa.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f6823a5ec0ab2c4c771d3da3ae356ef1e52464cf2e07c16b70e93c98bec0a874.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint f78d38e750e2b41a1943c1533684297bec36e258ad81f4d95eedeb567f01cfb0.
def localCycle00241 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint f7b3b4c9959237c480ab4c111987b80e7efc88fb9b0e76d7ad7d2c5fee4707ea.
def localCycle00242 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 4 0, .triangle 21 1, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint f83439f92779377bcd15a8ef9faa340b3b791722215ea5ed5c8bff67ddfeeb63.
def localCycle00243 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint fb8bbdf96d4344783fea80b80cecbc18a5618183fce2856519cb4637d5fee214.
def localCycle00244 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 19 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint fbd4573a869cb40317805a5c51136e21186f10d9658eb64747963d7e4162ae84.
def localCycle00245 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 0 0, .triangle 2 0, .triangle 19 1, .gapLower 1 0]

-- Cycle fingerprint fd6dd768c226ca23953efa62eb421a59f820654339508adb7b7bdcc0a91e03ca.
def localCycle00246 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, 0, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 19 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 0]

def library : Library := fun id => if id < 123 then (if id < 61 then (if id < 30 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 22 then (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))) else (if id < 26 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))))) else (if id < 45 then (if id < 37 then (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))) else (if id < 53 then (if id < 49 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))) else (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 57 then (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))))) else (if id < 92 then (if id < 76 then (if id < 68 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 72 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))))) else (if id < 84 then (if id < 80 then (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))) else (if id < 107 then (if id < 99 then (if id < 95 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))) else (if id < 103 then (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 115 then (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))) else (if id < 119 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))))))) else (if id < 185 then (if id < 154 then (if id < 138 then (if id < 130 then (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)))) else (if id < 134 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))) else (if id < 146 then (if id < 142 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))) else (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)))) else (if id < 150 then (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)))))) else (if id < 169 then (if id < 161 then (if id < 157 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 165 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))))) else (if id < 177 then (if id < 173 then (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))) else (if id < 181 then (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))) else (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))))))) else (if id < 216 then (if id < 200 then (if id < 192 then (if id < 188 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none))) else (if id < 190 then (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)))) else (if id < 196 then (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))) else (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))))) else (if id < 208 then (if id < 204 then (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none))) else (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)))) else (if id < 212 then (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))) else (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)))))) else (if id < 231 then (if id < 223 then (if id < 219 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))) else (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)))) else (if id < 227 then (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))) else (if id < 229 then (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))) else (if id < 239 then (if id < 235 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)))) else (if id < 243 then (if id < 241 then (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))) else (if id < 245 then (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![5, 3, 6, 0, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 1, 6, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 189 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10880)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 6, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 113 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10881)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 192 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10882)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 3 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10883)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 144 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10884)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 225 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10885)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 1, 0, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 122 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10886)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 148 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10887)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 1, 0, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 114 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10888)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 3, 1, 4, 2, 6], ![5, 3, 0, 4, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 1, 0, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 86 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10889)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 3, 1, 4, 2, 6], ![5, 3, 0, 4, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 1, 0, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 214 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10890)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 3, 1, 4, 2, 6], ![5, 3, 0, 4, 6, 2], ![5, 3, 4, 0, 6, 1], ![5, 2, 1, 0, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10891)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 3, 1, 4, 2, 6], ![5, 3, 0, 4, 6, 2], ![5, 3, 4, 0, 6, 1], ![5, 2, 1, 0, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 52 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10892)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 3, 1, 4, 2, 6], ![5, 3, 0, 6, 4, 2], ![5, 3, 4, 0, 6, 1], ![5, 2, 1, 0, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 3, 2, 1, 0, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 12 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10893)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 3, 1, 4, 6, 2], ![5, 3, 0, 4, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 1, 0, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 3, 2, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10894)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 3, 1, 4, 6, 2], ![5, 3, 0, 4, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 1, 0, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 3, 2, 1, 0, 6], ![2, 0, 1, 4, 3, 5]], proof := .tail 52 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10895)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 3, 1, 4, 6, 2], ![5, 3, 0, 6, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 1, 0, 6, 4], ![5, 2, 0, 6, 1, 3], ![4, 3, 2, 1, 0, 6], ![2, 0, 4, 1, 3, 5]], proof := .tail 78 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10896)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 3, 1, 6, 4, 2], ![5, 3, 0, 6, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 1, 0, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 0, 1, 3, 5]], proof := .tail 88 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10897)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 3, 1, 6, 4, 2], ![5, 3, 0, 6, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 0, 1, 3, 5]], proof := .tail 12 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10898)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 3, 6, 1, 4, 2], ![5, 3, 6, 0, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 1, 0, 6, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 21 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10899)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 6, 3, 1, 4, 2], ![5, 3, 6, 0, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 1, 6, 0, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 158 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10900)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 6, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 1, 0, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 1 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10901)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![5, 3, 6, 0, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 1, 6, 0, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 1, 6, 0], ![2, 4, 1, 3, 5, 0]], proof := .tail 14 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10902)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 1, 0, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 1, 6, 0], ![2, 4, 3, 1, 5, 0]], proof := .tail 1 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10903)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 1, 0, 4], ![5, 2, 6, 0, 1, 3], ![4, 3, 2, 6, 1, 0], ![2, 4, 3, 5, 1, 0]], proof := .tail 154 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10904)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 3, 6, 1, 4, 2], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 1, 0, 6, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 198 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10905)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 6, 3, 1, 4, 2], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 1, 6, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 150 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10906)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![5, 3, 6, 0, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 1, 6, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 124 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10907)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 6, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 1 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10908)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 1 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10909)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 154 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10910)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 6, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 161 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10911)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![5, 6, 3, 0, 4, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 63 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10912)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 154 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10913)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 81 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10914)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 1, 0, 4], ![5, 6, 2, 0, 1, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 136 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10915)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 3, 1, 4, 2], ![6, 5, 3, 0, 4, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 1, 0, 4], ![6, 5, 2, 0, 1, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 94 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10916)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 17 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10917)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 229 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10918)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 157 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10919)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 24 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10920)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![244, 160, 54, 32, 143, 108, 9, 195, 116, 82, 6, 37, 127, 240, 237, 235, 184, 107, 199, 16, 218, 13, 110, 162, 181, 92, 186, 18]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10921)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![244, 160, 54, 32, 143, 236, 9, 195, 116, 82, 6, 50, 127, 240, 237, 235, 184, 107, 199, 16, 218, 13, 110, 162, 181, 92, 186, 18]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10922)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 59 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10923)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 171 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10924)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 4, 1, 6, 2, 5], ![3, 4, 0, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![105, 187, 176, 95, 44, 118, 9, 125, 28, 197, 191, 245, 127, 40, 68, 29, 72, 107, 140, 224, 99, 13, 64, 47, 80, 205, 238, 120]) }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10925)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 233 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10926)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 208 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10927)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 137 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10928)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 59 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10929)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 137 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10930)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 171 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10931)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 4, 1, 6, 2, 5], ![3, 4, 0, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 146 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10932)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 4, 6, 1, 2, 5], ![3, 4, 6, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 147 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10933)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 4, 6, 1, 2, 5], ![3, 4, 6, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 4, 3]], proof := .tail 147 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10934)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 4, 6, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 4, 0, 3]], proof := .tail 83 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10935)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 15 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10936)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 128 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10937)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 4, 6, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 145 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10938)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 15 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10939)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 128 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10940)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 175 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10941)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 175 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10942)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 0 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10943)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 117 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10944)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 173 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10945)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 84 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10946)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 46 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10947)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 100 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10948)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 56 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10949)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 200 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10950)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 219 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10951)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 129 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10952)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![3, 4, 1, 6, 2, 5], ![3, 4, 0, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 112 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10953)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 190 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10954)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 22 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10955)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 174 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10956)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 4, 1, 2, 5, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 219 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10957)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 4, 1, 2, 6, 5], ![3, 4, 0, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 202 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10958)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 4, 1, 6, 2, 5], ![3, 4, 0, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 131 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10959)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 4, 6, 1, 2, 5], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 112 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10960)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 4, 6, 1, 2, 5], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 1, 0, 4, 3]], proof := .tail 112 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10961)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 1, 4, 0, 3]], proof := .tail 41 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10962)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 168 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10963)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 6, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 0, 6, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 134 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10964)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 51 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10965)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 168 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10966)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 139 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10967)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 27 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10968)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 27 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10969)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 3, 4, 1, 2, 5], ![6, 3, 4, 0, 5, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 74 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10970)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![26, 43, 61, 42, 2, 156, 172, 222, 79, 133, 39, 67, 185, 201, 97, 35, 106, 153, 70, 169, 60, 232, 206, 65, 170, 58, 19, 53]) }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10971)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 231 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10972)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 87 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10973)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10974)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 216 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10975)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 38 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10976)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 211 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10977)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![91, 25, 36, 34, 48, 215, 69, 23, 223, 133, 5, 141, 33, 221, 228, 193, 75, 227, 70, 167, 180, 177, 102, 243, 164, 165, 207, 151]) }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10978)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 5, 6], ![2, 1, 0, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 101 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10979)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .tail 135 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10980)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .tail 241 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10981)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 4, 1, 6, 5, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .low (![212, 98, 132, 89, 182, 71, 69, 23, 194, 142, 246, 31, 33, 221, 7, 213, 103, 227, 11, 130, 96, 177, 45, 93, 220, 196, 4, 209]) }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10982)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 4, 1, 6, 5, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![212, 98, 132, 89, 182, 57, 69, 23, 194, 142, 246, 31, 33, 221, 7, 213, 103, 227, 11, 130, 96, 177, 45, 93, 220, 196, 30, 152]) }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10983)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 104 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10984)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 49 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10985)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 4, 1, 5, 2, 6], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 0, 6, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 121 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10986)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 4, 3]], proof := .tail 49 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10987)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 4, 1, 5, 6, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 4, 3]], proof := .tail 166 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10988)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 4, 1, 6, 5, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 4, 3]], proof := .tail 146 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10989)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 4, 1, 6, 5, 2], ![3, 4, 0, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 146 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10990)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 4, 6, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 1, 0, 3, 4]], proof := .tail 8 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10991)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 4, 6, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 1, 0, 4, 3]], proof := .tail 8 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10992)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 1, 4, 0, 3]], proof := .tail 155 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10993)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 1, 0, 3]], proof := .tail 168 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10994)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 1, 4, 3, 0]], proof := .tail 179 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10995)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 1, 3, 0]], proof := .tail 168 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10996)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 3, 1, 0]], proof := .tail 27 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10997)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![3, 4, 6, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .low (![119, 210, 115, 73, 111, 90, 66, 20, 239, 123, 204, 77, 163, 226, 76, 109, 183, 234, 159, 10, 217, 188, 62, 138, 85, 178, 203, 242]) }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10998)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![3, 4, 6, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 1, 0, 4, 3]], proof := .tail 126 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 10999)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 1, 4, 0, 3]], proof := .tail 41 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11000)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 168 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11001)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 6, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 0, 6, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 149 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11002)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 4, 6, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 230 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11003)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 168 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11004)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![3, 6, 4, 0, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 139 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11005)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 27 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11006)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 3, 4, 1, 5, 2], ![6, 3, 4, 0, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 27 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11007)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (10880 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 10880 ≤ id.val) (hhigh : id.val < 11008) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 10880)) = true := by
  let j : Fin 128 := ⟨id.val - 10880, by omega⟩
  have hsum : 10880 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (10880 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard085
