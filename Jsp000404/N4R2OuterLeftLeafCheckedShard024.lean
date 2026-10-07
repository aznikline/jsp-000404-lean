import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard024
open N4R2OuterLeftReplay

-- Cycle fingerprint 0046add1510bd47793e325b099efeeb4347ef0e7598d0a6d01fd0a40bdb4bd0b.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 02496b69d38fc4c5f97b10b80ac7d9d7024cd7a9838f8d23eba723f56cb5c2ca.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0757cebba9acdc8def455ec375e60d025abac4d38f4f5c8e45b3d09df6c1fb15.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 07630a9256b8ab465a8c7f2be7fd77b285398969237c62ce9fce070f13636b20.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 0767da3a35232a7b4aba5c5346c548d5d7230e347a3e278333a47fe7fa539018.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 0bec27b0ca2b5d39361ab21a8a066f0258d9a63539e4c64c5dbf6382f1fa8c39.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 0dbd11454a667c5d96c8dca5c1ef1ba4913d168d4500c164e7116ef42f754b87.
def localCycle00007 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0ecdef038482eb93853accfbca2731dddd882b10b282d9a6324738b81306004b.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0f87001adf4326208981a4fe043729283fab5678a4909bb15378f78eb762efa9.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 0fd2b26f105dd0512c1f138af4de832ffeb1fc2ba58b9840c71770426f216a43.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 108eb2f08ade1798a98f3713952a119210b6ee76553dab70b49760182f66411e.
def localCycle00011 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-2, 0, 0, 2, 0]
    coefficient := ![-1, 0, 0, 1, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.gapUpper 3 6, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 118e7f0a78ae19430718ca1b93a4f6f1503abb8c2969ff3edd4399dd7d89c1c1.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .gapLower 0 1]

-- Cycle fingerprint 12d4e056473b37f3bf0a10ec2fba7fdb71379d667303e3429a79afbbe461499a.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 13f33c0f38363b72f052c73052cc25c5c9e30ab699a15d0a88c35fa6de335fec.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 14bd9bb685307c5404c157cc2642b26a5696c681f970257581b2ceefde84f2e1.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 14da458cb4e920fd924f845c48dc61f172c5dd00039c9ca7cf2908d33df1f401.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .triangle 6 0, .triangle 0 1]

-- Cycle fingerprint 158903999f7990c2ce967ce85e9c58c0c254b727b19e59b936b6c1a07cb6434a.
def localCycle00017 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 168dc00279a4dadd2e891bf310468eebb065eb4d9d5b21f120501c00733190ae.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 1749b29473096f1f1431b526d6a049180d17d921764caffefc77390261a144f7.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 19bc701f00fd343c56e73924f8d854414ea82d8abe327f36c0ec5d05f7539d03.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00021 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 23065613c3603aec1c44b6f137cce2d970b4e5c90ab3d238efa148eab8654b96.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4]
    constant := ![-1, 0, -2, 0, 0, 3, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00023 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 25069337ff217f87f7540036cbbad2ddd4d151fb8a121d9ca709438416c4ab5f.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2554fcf0696b97e3717faa7ab2796e2a68c4068ac299705ff528ef2c44955071.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 25de5126aa3429a7c487c4afde9c3aa66120766673ad5032c2f46063b18acce1.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 27fd9076423e8f017ee25eb5faf720e7ed4025fd7ec44df77f0d323489afd58d.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2b1a3202889fb47008b8ff86a7361dc2b3a236ec22f7eb629d8360c201825c56.
def localCycle00029 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2b91bac50c8db752556c0df3607107ebfe93fa050e1f3b1728ff85b0546cd12f.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 2bcf93967e60d73ad97b597244717b6e170ed985796bcb401728562f06193e57.
def localCycle00031 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 2bf0617241657e084b772c9a3aad08a513c9ca78cb6b52a2130d7e670c9bfe84.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 23 0]

-- Cycle fingerprint 2c2f9e741da46e205b4705708a2d53f3e497aeb50cc446e7b303238a8e99cf5b.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2dfba42b769d72dc733196571ebab7bc4614d0d09d709fd87ff225a84f464d76.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 2e15cff8013f2f227fd11f80221ac528e93b3dc1ff40ce45a4ce73613c647bc3.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 2f5006764bce48066982c3104f8c43ace2e956925e9529fb4921c2c641dfc0b3.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3051904ed865f88664cd15a117b8e40857cd01028e0e9f86b906dbcb287026f3.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 32e15e3230745da6cba2915ab6971351fc19ca4d8a7c526f04c547ccba36e8c4.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 35a6277855c7c950dd69693057ab3639ea252aadf0a958cc3dbd6848f9e43eb3.
def localCycle00039 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 37563f5bff8fc689f26bc0dcf8d8973f3b3e247c80d7852f15ad9b5e157d93a9.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 23 2, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 391402375facd85d6513782bfd2ac90f402a40cb5f27e9a8e2d7dd5fd905aaaf.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3ec3f5a987447352cfc09693602e2ed583adf4dd026947f35224f164fae58736.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 405a114aaa4c2cd930e3bea27ea91b3909fc3aba46b185cef6349f9049f90b36.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 443563070970df43959f2e926746a3c9f5f722341af3b2bf27803e37e676bd41.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 44858e22c6b1fb54e327ab781134248e24424c804d3928ffb565d73a9a8c9a4f.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 467a6c76321deaf4f9713386e2d75586ea040becb9361c8057a7ad187aa7a759.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 480e0c394b9eb1f3de08bfe9d3b3d5c41ca6e33cd4db0d2ac3461bf1cba83235.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 493eec554434b8ede6060f4675bb934d10e62ed817494f1ae8cafe792dbd99a6.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3]
    constant := ![0, -1, 0, -1, -1, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0]

-- Cycle fingerprint 4c4de2dc6c7e0c041dd39582a75dfcfb844a656ab3110cf291c899625992feb1.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4e3455f54b088113e388fccb71b857ae3fec72fb5777b03a7531e0b30ede0531.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 4e611817b5d5c20cfd8816b50512462ee69b7d000954a2a3f18dd13c2fb97ace.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 3 0]

-- Cycle fingerprint 4e649e75c824fd1ee0d565e0d474699eb27a679865b0c9a275e21e7a11e9f2ab.
def localCycle00054 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 4ed91d0263873d79a160e3330ce64464c2ad1ed2dd0736536ed0e7e4bcb34c07.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 5080d304008d3ac6e9d7325bae116c1c02a94665e9c20cc2f7896d81f229f98d.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .gapLower 1 2, .triangle 22 1, .triangle 28 0]

-- Cycle fingerprint 517824fba94f64f5ffb9875cf64b1e71a18a4ebc3a674a3a5d91283809f9fce8.
def localCycle00057 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 527c0a4f472c6da66bf99410c0f65564b7e329081941c7dc78ad21d2924c0b9a.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 537bca77ca200665947c0d91df4706a16a2c6d73ca64f1a288eda91f52a8cddf.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 2, .gapLower 1 2, .triangle 22 1]

-- Cycle fingerprint 54fd50cd24163f91e8f413b43eea00cf1a9d371e7fc1d4e39fe4159e150fe4eb.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 557a9a3067873f7f87cd621cd54e1b717271f137991bbb6c80260eada977c630.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00062 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 55e01f3d0d39558379bb5ca4dc1c26fc2d49c33116eb520c0041df1926262347.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 562f3d7ae9bf618f25cb713230bc81f9d0bc0e6a7912377af36f2d563e46addc.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 2, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 56bac1e5418536e6ed8ab2aed7051e7ee32b8d5b22eff10d975f618bc7459ab9.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 59cf3ba9ce17d2adaed24f04dbfb67bb6c26254e2f06b3fbac3484a109e5fabb.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 5b653f314b8cdfdf5b7a14a2e4ade751829bdb6d18c2fe4fae6a4e80f5004a6e.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00068 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5e76caef6d616057811b59f6c97c7c7cf3f7b0628ef97876fd0db8c3f7888604.
def localCycle00069 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00070 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 6055bbd4c7c04f3908d120b50dcb0f7844c9486e62435a273476121334499319.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![-1, -1, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 6116df656d06fcc743012622b3b4d08ac91bbaf6ce3dc5dbc3b65ca04b9c1bae.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 20 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 614cbc8c86f7de6d57bf24b34c939dffd4ad88808e4e18f7f45fb1636ad5e0ff.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 61ebacee2fe9af5ade61403aa7b875ebf97208bdf2a11fc0de025cfbd59b0c70.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 61ff67ef57b650646801544653694efca7fd3f27771054ba187139b8b4a48cb2.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 6246ed20ef0893f816bf8a1e363db6c2a7bbb7ad401a917c743662f6573e32ca.
def localCycle00077 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, 0, -1, 0, 0, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 625c64078baa7e3ad6beca1ec9a6ba17db127b313a012a5fdc7170d7661ed7ac.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 30 0]

-- Cycle fingerprint 62f8065966e5409616fe2ed14bf2454684787cff5a9c164c3e62e6333108dd29.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 649d0528c36f9bf7251de5ff5ef29c00432e903780f9e54f3dc67a6dc1a8b805.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 22 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .triangle 23 2, .gapLower 1 2]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00081 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 65ead236bb6ab0ffd98c10b8b2f4b00f1f24f702c2ed85f1f801ddba51c5f863.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 668aed4612c4d879cd68743c391be065f16418a43e8817278190eb40da6709f0.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 677af02f0369e15a6cb120a3a3d41f5c2d1faedd47f1c690176001e50e88f87c.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 67d03606e0f26909273e1d55805cd8ad73bc9bf503162c85601b796c52656989.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 6a0ec772326ef74e3606d60ce00c8caf9851811781e2dd5e74e8a3d4b043fc7d.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 6e5561a2bf02519384d37d5e9abc8ce7dfe6e24eb37fed7cc2ab4cb38704bc1a.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 6f1bd059710174828776de041e89299c68a317bd979c4cbdd27ee10bc7f01103.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 6f6463979d3e04665c6347d93bb980dba8599cea7325e09623b187ddadae7621.
def localCycle00089 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 709bf5e9c9f45159f34cff64eab904140de03dfbe2d02c6ef921f181dcbe1318.
def localCycle00090 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Cycle fingerprint 70aa20c9c2463a456d73127ecce6111bc960e58670a3540cd548466a3bb32625.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00093 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 76174a6fd7524be8ec8fbf5ff5d146737fe60f4f9b4dfd5bf8b15a09f8691fd4.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 794623e23f7876d2cea9b398baec81a95af9e03fc49512ce49b7533ca585e5b6.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 79bacc2c7797dafac7793e1bfa791fd6b12d64c47a7bd111e49d40b45c94762b.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 7a198589f61beaf02b8f27323e3e4a55fa7287e292799615e6c36f8a835a9ead.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 7a5c39c3dd6aef6fe51c65626ee4e4f9f13eb0f1d89dc8c3166e5bc9ef6536d6.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7de9fe481aa6220c5bc6ab3375d27c555fcf4646f57baabe18a5695104c78f2c.
def localCycle00099 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 6 0]

-- Cycle fingerprint 84119cce138f8f85a8efe090b4c4574efe75fd77ec65e5166b5c24d2364333f8.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint 848de51b729033a3465d22567a07d40f2ff45751c847796b8806713ea5bd8acd.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .gapLower 3 2, .triangle 11 0, .gapLower 3 0]

-- Cycle fingerprint 87e97e712aac240ee57943338fd8d00fdb881f0912d75901c7954a6ec321ef52.
def localCycle00102 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 5, .gapUpper 3 6, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 8e351f9fc92dc98e5b2580340c9bc0055bf9c54a4b673912cf5c8329f8022bf6.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 8ee14a3e7ff4a911e1c984d617a9c12be72027072b7f293e571579ea72d247f5.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8f958e8c6f140c90fa731014669dfb9221c028aecfe61fb89448a32babc29194.
def localCycle00105 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 23 0]

-- Cycle fingerprint 912575c235e9edf8d0ff4ced20dad0cff5bfd6880d0be72610597620d89ae3de.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 91cb2fabc2080c47bbad219ed43abf9b6b4252d07260b2bbb8f207a5b777dfa3.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 92cb35304d1a4efec069b187e8a4931c4ef214ea31fca8db8d9daa7f6cb6a6b2.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 96b1a0962619ad1883f29f0cfda842acba6539633c5d5e07fdbdcabfecc96311.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 98834c5bd1d1dad991fe211244c1b22ce8c816623ed482221e6986eb80ad22d4.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 9a2d618a3392b7e70570a2aec1301c3eafb403386cc568d9f3094355e81b1b57.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 12 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 9bbbf7e78e614fda06718effb6c51ee6cb3a6c2cf77084aa6a9b726a80ad77f0.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint a1981309059f7072481996bb1c48d901a9b2d83a767f31bd10f77768c125e824.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 6, .distance 2 5]
    constant := ![0, -1, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 28 1, .triangle 6 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 15 0, .triangle 27 2, .triangle 30 1]

-- Cycle fingerprint a2eff47b36734f173eee0156d90208f98f6e7c5967a5708c2eedeccc715eb65a.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a33be4089faccf029e26f97c18a952b1e4f08b8dbb397e4f42a2f50659089d40.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .gapLower 3 3, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a42e916cff90a41ac0a295042c06eefbc395b7d630d3093817dd5b28db44cced.
def localCycle00116 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-2, 0, 0, 2, -2]
    coefficient := ![-1, 0, 0, 1, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.gapUpper 3 6, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint ae6881d24750c2c32eac4263726beee0fd73b8bf6f31bd231b6ca44c5e64f9c7.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint b3e2dc620f2760a21d18fc005e4c80b113f497e19516741e8de3f207dbc6096c.
def localCycle00120 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 15 1]

-- Cycle fingerprint b41084b83046950b98754ebf730bfe5dda08ff51a48df31f24fe4ade8a958ef6.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint b432804b4a29924b13e0498089b58fbd86a84910e76e670c19b32206caefa9b8.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b559e02593a38d9bed582eb7184cbe7ff7a3cfb7b6a69d15a9fa0ed5408e90a0.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b61fd472ea0fb26ced74db41d30eaba94edf04d0b1e94604a53c13d746a53a67.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint b6ef032a119df75ea7eb452f4a76c49a8edb5109bc33cc8e7130094256ccc45f.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -1, 0, -1, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint b7ef812ea580f748495028786b53f2b692bc7a437caec600c0b7f484e47c7a7d.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b90faba7513d3d628101fa0943cb471acc68430c47e56acc2cca1bd074a86e7b.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint be5ad2b2125a82904a3f92da1dafa965d91fad9522e66e8dcf6a597f0705665f.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .theta 6, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4]
    constant := ![0, -2, 0, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, -1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, true, false, false, false, false] }
  origin := ![.triangle 23 2, .gapUpper 6 6, .thetaNext 5, .thetaNext 4, .thetaNext 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0]

-- Cycle fingerprint bedb9dc937ec868e027d345a42b5c2c1740238facd5cede0b9a3c216829bcda2.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c197d619419a41b7fa517e627773280a56579a81ea36e2c9683ff1f42d8865ec.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint c1deaeb7764b53873903a24434b711e1bfd0343c74ddfe7095cefead4c758d20.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c250c06ef9de5ba97895db8477bbb6f54945fbf7d727fda4e335c0bc4d15a11a.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c392e000da2c54379b4576a2e64d7138fd37d78c7e5c11ffd4639ea112c09775.
def localCycle00133 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint c4faa0dd71d91dca45ca9e43747caf186c2c377cd4cad820ba41237a62fd7178.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00135 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint cc6c1ce4bb1a73b78e81afbd90617ba24e4a983bb29be0bdbbf9dae651e1915b.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ce7a6d7002be177f3748f4ff4f23ce828038f25ba9b3a910013727096a1ebb1e.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint d3935ee0b6fe9e279da447e504af8c9c1e548e746158ed86108d08b6c0e0ff6c.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d4bb3bf206a830cd71f8535a6ef736a20f0a08b33380c3613ff5ba9a08691d44.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d5f40763bb168e318e78b818383954500ffe3337ad609bf91b101a596794b4df.
def localCycle00140 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 2, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 2, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.thetaUpper 2, .gapUpper 2 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d71d6bba5bb35fe1510e48160f50a0764d981c28d59af0f645902c622ede0ca5.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 9 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d93851b556ac60e2b56706eeb0adf8dcb94a58559f45d73e901c2d62a2e5005a.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint d9a3c14f35450f92b6881056213d79c996ab0f808f350939ff1e96a75af2df66.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint dc1c3118e1872cb9e78e1ccb9a8b913594d8eb92246d7c709c3da072cf60f515.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .gapLower 0 1]

-- Cycle fingerprint dcdcb4ae06b850c30b7774091fcce8fb5a220b98768ee76c78c49785006d8d78.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint e2756af3af9e3b4c91f1923aedb5248379eff361bc98741fb244d1c6661baf48.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 29 0, .gapLower 4 3, .triangle 9 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e3ea62a3f12113703bcfc09ca77035b24e5a799ef4fff00dab4938835ef22823.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint e633f2abf4933741cc1b4b712671d1d11596d08d2e7e21ead78f1d2cb3dc05f9.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint e93e1a1e113329f1bba856be3960dfefea04e4035079ad76bfca792031ab90e9.
def localCycle00149 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 24 0]

-- Cycle fingerprint ea15d8dd7efed6a5a6ea07ea24bcc932cae0525176ab98a8dab035e86c9978ca.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint eb6241ff1d693bc846576ed7c838b36149cb3eb825a746ff290b4509e460dea9.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ebb9ef2238a511d3e14216bf76e58b0aa0e19d3e3c595892f3a418e5e43e93bd.
def localCycle00152 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ed654f9dcf3507ab56824b08522e68a57ea734f43726d103cfe8755841cc6b81.
def localCycle00153 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ed91a566d87fa75fddf3d34dce7d2921dcdba4694f4c928c8765840a3ab34c66.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint ee2df6a66530307462c1efeb6892d781412768216604a96b1e9319359d4f1905.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint ef1375e6bdee8e410acf2bf1525012324119adfb6b27ad7c44d316e4d3d812cd.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint f318b5eec8a0bfdb8e02869f8589fbdf0273817345c25baa6185da75f8e4fb4b.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f3fbc9ecc27064603d7bce22416d777c0f43c5e7556398e80f2972d0e33bf90a.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .gapLower 3 3, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint f431c49709af933635b8035b70f6b6c3c3a2ad39839701763dcdc35f7553be37.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f43c3d54d5e1ae98b8dee3c8da0e6e4e5ebc03427c15e87108c8f24e745bf749.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint f466d3cfaaed64ef5ead9d918275cd71109948a5f9105a3826c2f9c644b82ab8.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f6545692abb6e81a5974b81be529c32c7a619e7eaf8f9b91c6b731efad2a443e.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f722cf157794c80e22eaa77583ee96315a68997cb5fca7387cb187627137d443.
def localCycle00163 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint f7e82ba8beaab69f2b71d00b9aa7c5e467d65c9f71f8048bf350df35b849dd3f.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 16 1, .triangle 6 0]

-- Cycle fingerprint f916cc537e4bca96fac2ab6c97a7fad1bdb2d3abeef208ecded2ac621ecb7b35.
def localCycle00165 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f93f4bae1cae67952bb322acb904a6a370f1bc97e5b4a18e1d2bbd7bf648a630.
def localCycle00166 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4]
    constant := ![0, 0, -2, 0, 0, 3, -2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0]

-- Cycle fingerprint f9d0c195b1235283f0f9fe7abbaa4257832f9f7d2cbeb8ad2b45bf210abdbfe0.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fa15194f52beb93a13b3cd41f85cc206e11843c9ca5209000ffd5d41c7cea714.
def localCycle00168 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint ffea61a06f15b810d616f97cffbaa096a98b0a7d7a607b7f1317ff691d15f793.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 2 0]

def library : Library := fun id => if id < 85 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 74 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))))) else (if id < 79 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))))))) else (if id < 127 then (if id < 106 then (if id < 95 then (if id < 90 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 100 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))) else (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))))) else (if id < 116 then (if id < 111 then (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))))) else (if id < 121 then (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))) else (if id < 124 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))))))) else (if id < 148 then (if id < 137 then (if id < 132 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))) else (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))))) else (if id < 142 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))) else (if id < 145 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)))))) else (if id < 159 then (if id < 153 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))) else (if id < 164 then (if id < 161 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))) else (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![4, 5, 0, 2, 1, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 168 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3072)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 1, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3073)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 8 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3074)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 24 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3075)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 28 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3076)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 28 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3077)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 110 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3078)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 1 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3079)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 1 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3080)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 110 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3081)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 43 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3082)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![5, 4, 0, 2, 1, 6], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3083)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 1, 6], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 115 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3084)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 158 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3085)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 6 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3086)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 151 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3087)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 6 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3088)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 91 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3089)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 138 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3090)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 6 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3091)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 33 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3092)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 153 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3093)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 2, 1, 4, 5]], proof := .low (![95, 117, 21, 167, 61, 120, 62, 92, 9, 157, 109, 102, 113, 114, 75, 65, 102, 11, 16, 164, 102, 169, 14, 102, 17, 102, 7, 116]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3094)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 2, 1, 5, 4]], proof := .low (![71, 72, 135, 67, 61, 120, 62, 49, 27, 10, 109, 102, 113, 47, 31, 65, 102, 118, 2, 5, 102, 5, 14, 102, 17, 102, 7, 116]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3095)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 1, 4]], proof := .low (![140, 68, 93, 23, 149, 120, 62, 42, 4, 104, 89, 22, 81, 127, 52, 35, 137, 130, 3, 35, 137, 73, 78, 148, 133, 76, 156, 142]) }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3096)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 132 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3097)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 132 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3098)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 154 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3099)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 4, 1]], proof := .tail 82 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3100)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 82 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3101)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 82 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3102)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 60 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3103)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 4, 2, 1]], proof := .tail 44 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3104)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 4, 2, 1]], proof := .tail 44 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3105)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 6, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 44 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3106)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 0, 2, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 4, 0, 2, 1]], proof := .tail 44 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3107)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 44 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3108)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 161 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3109)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 123 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3110)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .low (![125, 165, 70, 163, 32, 120, 62, 29, 53, 139, 77, 166, 81, 94, 37, 105, 85, 100, 56, 59, 80, 40, 58, 64, 39, 84, 144, 12]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3111)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 99 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3112)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![3, 0, 2, 5, 4, 1]], proof := .tail 57 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3113)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 2, 4, 1]], proof := .tail 131 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3114)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 2, 4, 1]], proof := .tail 131 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3115)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 154 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3116)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 4, 2, 1]], proof := .tail 122 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3117)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 4, 2, 1]], proof := .tail 122 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3118)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 6, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 122 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3119)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 0, 2, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 122 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3120)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 0, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 122 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3121)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 0, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 98 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3122)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 18 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3123)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 45 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3124)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 38 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3125)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 48 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3126)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 143 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3127)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 43 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3128)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 5, 2, 1], ![3, 0, 6, 4, 2, 1], ![3, 0, 5, 4, 2, 1]], proof := .tail 106 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3129)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 5, 2, 1], ![3, 6, 0, 4, 2, 1], ![3, 5, 0, 4, 2, 1]], proof := .tail 111 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3130)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 6, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 51 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3131)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 0, 5, 2, 1], ![3, 6, 0, 4, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 134 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3132)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 0, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 134 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3133)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 0, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 41 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3134)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 18 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3135)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 36 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3136)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 48 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3137)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 97 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3138)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 143 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3139)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 43 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3140)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 48 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3141)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 143 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3142)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 43 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3143)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 79 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3144)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 5, 0, 2, 1], ![3, 6, 4, 0, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 0 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3145)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 5, 0, 2, 1], ![6, 3, 4, 0, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 51 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3146)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 5, 0, 2, 1], ![6, 3, 4, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 41 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3147)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 46 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3148)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 146 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3149)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 136 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3150)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 141 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3151)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 136 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3152)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 152 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3153)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 136 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3154)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 136 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3155)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 152 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3156)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 152 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3157)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 74 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3158)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 74 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3159)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 103 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3160)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 103 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3161)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 5, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 107 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3162)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 5, 4, 0, 2, 1], ![6, 5, 3, 0, 2, 1], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 159 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3163)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 155 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3164)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 66 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3165)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 145 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3166)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 63 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3167)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 4, 3, 5], ![6, 0, 1, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 25 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3168)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 4, 5, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 54 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3169)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 55 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3170)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 128 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3171)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 150 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3172)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 63 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3173)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 30 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3174)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 13 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3175)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 3, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 96 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3176)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 3, 5], ![6, 0, 1, 4, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 20 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3177)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 3, 5], ![6, 0, 1, 4, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 15 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3178)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 3, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 121 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3179)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 5, 3], ![6, 0, 1, 4, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 87 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3180)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 5, 3], ![6, 0, 1, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 55 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3181)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 4, 3], ![6, 0, 1, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 34 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3182)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 4, 3], ![6, 0, 1, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 147 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3183)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 3, 4], ![6, 0, 5, 1, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 112 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3184)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 3, 4], ![6, 0, 5, 1, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 96 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3185)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 4, 3], ![6, 0, 5, 1, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 108 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3186)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 4, 3], ![6, 0, 5, 1, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 160 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3187)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 2, 3, 5], ![6, 0, 4, 1, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 88 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3188)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 2, 3, 5], ![6, 0, 4, 1, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 50 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3189)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 2, 5, 3], ![6, 0, 4, 1, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 19 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3190)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 5, 2, 3], ![6, 0, 4, 5, 1, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 26 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3191)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 4, 2, 3], ![6, 0, 4, 5, 1, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 119 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3192)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 4, 2, 3], ![6, 0, 5, 4, 1, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 101 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3193)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 4, 2, 3], ![6, 0, 5, 4, 1, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 2, 1], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 83 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3194)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 0, 3, 1, 4, 5], ![6, 0, 2, 1, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 162 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3195)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 0, 3, 1, 4, 5], ![6, 0, 2, 1, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 129 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3196)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 0, 3, 1, 5, 4], ![6, 0, 2, 1, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 69 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3197)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 5, 4], ![6, 0, 3, 1, 5, 4], ![6, 0, 2, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 124 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3198)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 5, 2, 4], ![6, 0, 3, 5, 1, 4], ![6, 0, 2, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 86 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3199)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (3072 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 3072 ≤ id.val) (hhigh : id.val < 3200) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 3072)) = true := by
  let j : Fin 128 := ⟨id.val - 3072, by omega⟩
  have hsum : 3072 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (3072 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard024
