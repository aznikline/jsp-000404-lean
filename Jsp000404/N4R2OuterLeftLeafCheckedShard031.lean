import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard031
open N4R2OuterLeftReplay

-- Cycle fingerprint 01c0c6a6d44469bbfb9fadfccbcc180687ae1a9f6fd591c05454447a84889abb.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 0483dcf633cd7728eeacf7d117ec3cfc44ee3d6b26ca5819dff9bcc83fe6a8f6.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 05942d5961c856f2df5bbb7d1f78c00089e3e0e4fdaf1f629555aaac91c64a62.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 0686bb8d0c0426f2d5c8740ae2fb310294a9c54d629ae4bb8d6d763b0adf6300.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 15 1, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 08b6cb5b82f29781a2f584c8bc7610f0e778df8b9b87aebadd9febae966a27a3.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 0bb590a651f03be03c66f0efb4c4c479f63c3f70706d050072bfa8fa22bb8ba6.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .gapLower 4 0]

-- Cycle fingerprint 1a3a309338ceecc01f922f0da68fc446e9c6b7b3266942cba2ee2e6c3c0afd97.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 1d1ac0e7709449378ff1f78c8d404e009dded3224b6663936c319f638725dbe0.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 27f2399117df7feaaedbd9f36d6dc84d392a0d151e2f5a56935d5bbee6361871.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 2c588bd75aa45b73515e05ad9762e7f830f103452dbb71fa0bd475e6ee3ef101.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2f71b45bd54b1a3ce913c634c2df6f3fc13f21c5d38ec2a09e0bf36bd5516eca.
def localCycle00010 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 5]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 0 4, .triangle 6 0, .triangle 28 0, .triangle 31 2]

-- Cycle fingerprint 34364e4ba94950a7972409379e7046a5157dd4fd063b51fa161c084eddfda54e.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 36822d7c4a1a7834fe94d72ccc3573eada307ca7bbef2dd69b1cfadf2070f0e6.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 36d9559ba100fc0be2a8cf42feb63f7a970b4189b5df917d775efc209052b3af.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 382be7c2862699b4466a51eaf44f596802386b10da64da92ee94e3d73a812252.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 3c97c9069fa7ea5b598d9fbf53e7e0d22da9fb3805902e8d2382d5b18a668d69.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 3fd601c75c02ca5ee9ae1781e4905ce55a4caa517013cf22494987a94c16620d.
def localCycle00016 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 4214526be00b536d1bcc4fb9361e15be2d92680e2aaab95212d3deb6310a8f8c.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 4b829822598ea7d6413eb2eee505522387e7571441516d554de07fb8f4b73e31.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 4d45e2340e99719e8ce33a61fb13a1be6fe90eb14cc711834a4d44d0aa6428a6.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 26 1, .triangle 5 0, .triangle 6 0, .corridorLower 2 4]

-- Cycle fingerprint 516fa0897a43a287bd7d436def0d04deabf29adbf9f2f678f2b6b107b9891f37.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .gapLower 0 4, .triangle 6 2, .triangle 12 0]

-- Cycle fingerprint 56443e1234d467bb338eef03fb1d1eab211bf92c977bd5aeeead122cecd4743d.
def localCycle00021 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 5b80780e43bb33a5d2934883fcb9e215b4faf3846b2c7c67f4a1c2ab2151a779.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5dcb5dba417262ab21e0e5ef9bfde3201156fc4a6e14de0af74d6aec99f7daf8.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 693a1458d258ae1f86c24293dbfc12da341952ed47a3cad580617d2bf05f8dd2.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 6cdb5dfc195c5b6fede2d6cd80e55b4eb38f23662952c5a10493281cbc71c224.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 7416543d4e1db464ce16bb2e7f6e771c30a40927d796e42a83e86b05660b3d27.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 76b44ac93a57e8f982ca68d4d7fb9b81bc9c9c6b93858f85fd9f2e927715595e.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 77f643797ac7612e91bff98d801c5f505aaf808e82d27971540481d311e64864.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 78dc2cdb71f26f137181847c22fb1d117d544e77fa5a6a99fc6b91ff3bca27c3.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 79087b06c04798eac748fb2f12c6c82476573ecde7fe2d6a4bf525492f1702e9.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 7bb8d45c15b088612c85b30e47f47d86d8f2b01877d47c52c528e7472e76e581.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 864a0e9dbecde62fb6330a5b366ccc3d8c66f9793dc44e3cdd77f8f9b991ff0d.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint 86dfcfeeecd84a2be25949eb96943c47f53ec66ae333bf61dff949bde9f49386.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 8829fdecf88db7c5dc4c27fb1fe6776282d2bb0d1b46af7276c2b80a755d0036.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 929f5cd066cfbeaf12bbf59a607992ea1d19c5f315a35459a97072571509b2fd.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 936f68ad1324f7f0fb38426b7378ddb756e951721ceadbae61a7b084564e26e8.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 956d1278722927055f62fa8bffa9618f85d0e48a015c280b37e1d667d9b05b9b.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 957800209f369908ddb9c41eeed7f70673073eef9aa3f96bd84eba902b0e1c3c.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 97f2b5b2a74233a9df39097ec0610d113527a3fd7388bf84ddf918c9684a43b9.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 3, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 2, .triangle 22 0]

-- Cycle fingerprint 994a7646d6a1be00b8f14a3b925b5f879986060143a1308160a8d37ff52d961c.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 9b18e6736c080d55e0c95c80c8b1a1e84bc6295882ea2717dfba8fe06977b617.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 4]
    constant := ![4, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .gapLower 4 0]

-- Cycle fingerprint 9b5f7b0904052a5a9d6d0baf4981bd8b5dbb275316c5729f1f3b9db2cf3910c8.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 6 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9bb4726845c7c0973e2041e989797f41870361c76d1fc2c2c23a026104455d8a.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9c9cf7b56012bf0f338aeb954602ff5e2aa5024a62d6cd178a5a02cc5b1e0f78.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9d91f8385eac9c787f226ba06c72e06cbc928d0fde0051356f72c3ab26376332.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint aa116368678123ad409d0e489b9c10d95ca685ed05e0acf8df5cd819e64a0fb0.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint b16b6dcead6b91ae9b3167e8b94d2fd568b05662b98237dc42bc2e22067cff6e.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint b30a6bb1506068dd2b0fb8dbde88e836439f8eb96ce63b25c06cf5f8e7a38810.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Cycle fingerprint b8a2afb31e3d5bdd2c81362f2ae718cfc844e285f3418ae430485f27de9490ea.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint bb47bf1f13d97b4d17e4ae08342dad826ac54aa971950b44cfa632de587b77eb.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c2669b6f1136bb1cd3401b5cbec889e0f211b2282b9dc77bdbf84f735bc956ad.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint c523925cec2a96bc8c4570346ed39c0bcd9ededffa5d27633b994334c25a4667.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c93a84ceb81b72e4ff304b3125155a122339bf1ccc492c293d48fc24b8c90d15.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint cb0bd16b30f3df61fbd387bdeca34c87d609e5408dc1e03ebde8aa400748647d.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint cf51d846b26f0d176fd7e860e92ed1e9fdd03dbec52517f8fb8ad30345bd5396.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint d7cbec7bd93fd3cde380a1e0ba730e68d77c1344caf19c528a60d647387a44f1.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d9459114e2c1adfcc59ee7207c456028998296a881e9f35b7914052fc6d9eeec.
def localCycle00057 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint dcb4c8f26cafc48569caa37a2cfe906af99be6f05bab2f9ac7c10abb4ce3a42d.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dd05066571d17efc2588a65c19a35213fd1b443cff964507b9bc2275707419e4.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint ddd00c628d75e65ef5068f86803219b9824fbae050a898894b5dfeed3b574389.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 10 1, .triangle 5 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e1d58afc53978c70d4ea830a7d562d0d2c636ae89a7d1e5ec1cc8ed81753aa18.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint e52258055e88fd7a75a685af38a87ee50498d442e88d3c7904611f8181ad7119.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint e5c865a09ccd674db42c0e4223e81da1db4551e746e9ba4a4fc0a135ff3d7fac.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e760a1f8bd0c899a738fff3a4edd1091ad3f3e7f0faf44e2de445f03a7152664.
def localCycle00064 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint e8005734986468466a6cfce9470e9281ca129c2afb694a20bdae59d78e3406e8.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, true, false, false] }
  origin := ![.triangle 16 2, .triangle 22 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint ec4db78f18059ed7055865f30e783e6cc1ded33736cf6603cd23c9608112589f.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint ee9a56fb3dec47a1a354884ed110d62ed5de23b340f7ffa5d2635d645957cc38.
def localCycle00067 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint ef94bcbbe37a5de2e06b250684329ed009eb25da33d749b27bddf69c18066aa0.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint efcf62a39ffe3c8a4eb19576a9d78be1aab2f425260f750ff6536568b3f632d4.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f252956f053d97d7a057512f95dfb01c1a68f64e7b82d4390c05b968bac7a2e2.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint f31fb5d6e0316ee23334050f91a2d3b39255aebb74e641260585f29383b83692.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint f575fb4e5d266d88f4ae596dcf5753ccafa1701f49ece61b0feba7ba9f6e3b9c.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f6da4664ee310d76b245729828857409e8103026ecfac1b219e002e0b6c20e64.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint f8042efea723304dffbdb65cdda0e2f905ab6b05b8e48f973efb6e748bf908ff.
def localCycle00074 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint fd3ff69e3f22569a1b096d40482f2849701128246d22de41872a5475436e364b.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint fdfceabf41be6f98271e9e8f3b28d593fc81fe92253c3e4e045cc2a20cca292f.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint fe5c2e51d4672fe13db857e47e625a65f0703f034b4daccee15b956f0828fcb8.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

def library : Library := fun id => if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 58 then (if id < 48 then (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 53 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))))) else (if id < 68 then (if id < 63 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))))) else (if id < 73 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 5, 0, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 65 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3968)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 39 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3969)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 5, 4, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 67 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3970)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 5, 4, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 72 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3971)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 5, 6, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 59 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3972)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3973)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 62 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3974)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 5, 4, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 67 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3975)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 5, 4, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 72 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3976)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 5, 6, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 59 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3977)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3978)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![3, 0, 2, 5, 4, 1]], proof := .tail 62 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3979)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 5, 4, 6, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 72 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3980)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 5, 6, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 59 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3981)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3982)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![3, 2, 0, 5, 4, 1]], proof := .tail 46 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3983)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 2, 6, 0, 4, 1], ![3, 2, 5, 0, 4, 1]], proof := .tail 46 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3984)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 2, 0, 4, 1]], proof := .tail 49 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3985)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 67 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3986)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 4, 1], ![3, 2, 5, 4, 0, 1]], proof := .tail 56 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3987)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 75 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3988)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 56 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3989)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 18 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3990)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 18 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3991)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 5, 0, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 73 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3992)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 5, 0, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 65 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3993)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 20 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3994)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 64 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3995)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 42 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3996)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 6, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 26 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3997)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3998)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 4, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 64 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3999)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 4, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 42 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4000)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 6, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 26 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4001)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4002)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 69 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4003)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 6, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 26 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4004)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4005)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 35 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4006)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 44 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4007)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 54 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4008)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 5, 0, 1], ![3, 2, 6, 4, 0, 1], ![3, 2, 5, 4, 0, 1]], proof := .tail 27 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4009)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 5, 0, 1], ![3, 6, 2, 4, 0, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 0 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4010)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 64 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4011)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 5, 0, 1], ![3, 6, 2, 4, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 8 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4012)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 8 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4013)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 5, 0, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 45 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4014)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 4, 0, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4015)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 4, 0, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 10 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4016)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 6, 3], ![5, 4, 0, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 74 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4017)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 6, 2, 3], ![5, 4, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 61 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4018)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 6, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 34 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4019)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 6, 5, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 14 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4020)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 4, 2, 6, 3], ![5, 4, 0, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 74 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4021)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 4, 6, 2, 3], ![5, 4, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 61 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4022)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 6, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 34 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4023)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 14 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4024)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 2, 3], ![5, 4, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 24 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4025)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 6, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 34 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4026)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 14 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4027)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 43 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4028)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 14 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4029)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 77 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4030)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 28 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4031)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 44 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4032)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 54 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4033)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 2, 0, 1], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 23 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4034)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 2, 0, 1], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 12 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4035)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 74 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4036)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 32 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4037)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 4, 0, 1, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 70 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4038)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 3, 6], ![5, 4, 0, 1, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 71 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4039)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 2, 6, 3], ![5, 4, 0, 1, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 71 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4040)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 6, 2, 3], ![5, 4, 0, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 53 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4041)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 6, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 11 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4042)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 6, 5, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 22 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4043)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 4, 2, 6, 3], ![5, 4, 0, 1, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 71 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4044)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 4, 6, 2, 3], ![5, 4, 0, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 40 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4045)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 6, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 11 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4046)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 0, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 22 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4047)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 2, 3], ![5, 4, 6, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 4 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4048)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 6, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 13 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4049)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 52 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4050)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 6 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4051)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 52 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4052)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 4, 6, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 33 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4053)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 9 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4054)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 9 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4055)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 9 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4056)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 50 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4057)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 58 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4058)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 52 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4059)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![5, 6, 4, 0, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 33 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4060)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 50 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4061)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 2, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 63 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4062)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 2, 3], ![6, 5, 4, 0, 1, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 2, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 30 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4063)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 0, 3, 1, 5, 6], ![4, 0, 2, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 29 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4064)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 0, 3, 1, 5, 6], ![4, 0, 2, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 5 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4065)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 0, 3, 1, 5, 6], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 37 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4066)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 2, 5, 6], ![4, 0, 3, 1, 6, 5], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 57 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4067)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 2, 6, 5], ![4, 0, 3, 1, 6, 5], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 31 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4068)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 6, 2, 5], ![4, 0, 3, 6, 1, 5], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 55 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4069)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 6, 3, 2, 5], ![4, 0, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 36 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4070)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 6, 3, 2, 5], ![4, 0, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 51 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4071)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 6, 4, 3, 2, 5], ![4, 0, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 38 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4072)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 6, 4, 3, 2, 5], ![4, 0, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 2, 0, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 51 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4073)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 4, 3, 2, 6, 5], ![4, 0, 3, 1, 6, 5], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 31 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4074)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 4, 3, 6, 2, 5], ![4, 0, 3, 6, 1, 5], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 55 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4075)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 4, 6, 3, 2, 5], ![4, 0, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 36 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4076)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 4, 6, 3, 2, 5], ![4, 0, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 17 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4077)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 6, 4, 3, 2, 5], ![4, 0, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 38 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4078)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 6, 4, 3, 2, 5], ![4, 0, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 17 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4079)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 4, 2, 6, 3, 5], ![0, 4, 6, 3, 2, 5], ![4, 0, 6, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 1 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4080)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 4, 2, 6, 3, 5], ![0, 6, 4, 3, 2, 5], ![4, 0, 6, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 76 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4081)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 6, 2, 3, 5], ![0, 4, 6, 3, 2, 5], ![4, 6, 0, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 66 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4082)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 4, 6, 2, 3, 5], ![0, 6, 4, 3, 2, 5], ![4, 6, 0, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 66 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4083)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 4, 3, 2, 5], ![4, 6, 0, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 2, 6, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 48 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4084)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 4, 3, 2, 5], ![6, 4, 0, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 6, 2, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 41 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4085)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 4, 3, 2, 5], ![6, 4, 0, 3, 1, 5], ![6, 4, 0, 2, 1, 5], ![6, 3, 2, 0, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 47 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4086)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 5, 2, 6], ![4, 0, 3, 5, 1, 6], ![4, 0, 2, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 21 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4087)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 5, 6, 2], ![4, 0, 3, 5, 6, 1], ![4, 0, 2, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 25 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4088)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 5, 2, 6], ![4, 0, 3, 5, 1, 6], ![4, 0, 2, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 15 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4089)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 5, 2, 6], ![4, 0, 3, 5, 1, 6], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 16 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4090)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 5, 6, 2], ![4, 0, 3, 5, 6, 1], ![4, 0, 2, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 3 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4091)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 5, 6, 2], ![4, 0, 3, 5, 6, 1], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 7 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4092)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 6, 5, 2], ![4, 0, 3, 5, 6, 1], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 19 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4093)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 3, 6, 5, 2], ![4, 0, 3, 6, 5, 1], ![4, 0, 2, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 60 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4094)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 4, 6, 3, 5, 2], ![4, 0, 3, 5, 6, 1], ![4, 0, 2, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 68 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4095)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (3968 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 3968 ≤ id.val) (hhigh : id.val < 4096) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 3968)) = true := by
  let j : Fin 128 := ⟨id.val - 3968, by omega⟩
  have hsum : 3968 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (3968 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard031
