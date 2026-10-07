import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard006
open N4R2OuterLeftReplay

-- Cycle fingerprint 00811b7dbba1129fb2e7246ced7275877c5de4cb254b56b8a1ed77e2c379a316.
def localCycle00000 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 28 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 014ccaf225203d801b292a1327fc0511d7ea77cb21feac6165ed06cf973b5e04.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 018e1db27636a214ce20e3a9a2e303dbec94b51a8edeeb06133eecc14c9ee307.
def localCycle00002 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1]

-- Cycle fingerprint 02fba61ef657d18e22d3ca4cf9bfa883fa1d7b0a79a58fa968a1cf28cfa644cb.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 053925899e6587d9b1b7b3e3e9f8f14d0470934bfcca14b691bd297446e09058.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 0757cebba9acdc8def455ec375e60d025abac4d38f4f5c8e45b3d09df6c1fb15.
def localCycle00005 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 07630a9256b8ab465a8c7f2be7fd77b285398969237c62ce9fce070f13636b20.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 0767da3a35232a7b4aba5c5346c548d5d7230e347a3e278333a47fe7fa539018.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint 077973d2a868b651f005100c93bd0d16b4f3527aacc0e828179863866e0a5068.
def localCycle00008 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00009 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 0851ac38f730f2a998aeb61ad1f82f1bcba3cbac84e3bd13189455c4c54d7fe0.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 098c68d469829de5da54a5e4ce479da5f01a205908fde4f290a1f91334a4375c.
def localCycle00011 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 099ebd9d17930291d1bd70069eaff1d3de183e2e8f4d7dc32b83707cb092870b.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4]
    constant := ![0, 0, 0, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0]

-- Cycle fingerprint 0a57a463c37d8b762387042e8445b0388fa5fc9f84da5ffe8255b04487855653.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 3 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .gapLower 1 2, .triangle 19 1, .triangle 25 0]

-- Cycle fingerprint 0c41b1c874788fe21a68e186c5734c18c5decc9222e3a0a9ab6a8a669d1e277c.
def localCycle00014 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint 0d957309910edd7067568f46469a7c2e042686da506e1ec0d2ddd4ed6d40a79d.
def localCycle00015 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 0dbd11454a667c5d96c8dca5c1ef1ba4913d168d4500c164e7116ef42f754b87.
def localCycle00016 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0f87001adf4326208981a4fe043729283fab5678a4909bb15378f78eb762efa9.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 0fd2b26f105dd0512c1f138af4de832ffeb1fc2ba58b9840c71770426f216a43.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 118e7f0a78ae19430718ca1b93a4f6f1503abb8c2969ff3edd4399dd7d89c1c1.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .gapLower 0 1]

-- Cycle fingerprint 13d898c146d9ffffb891ebe2e4b5bf65b9cdf827949aefccc2af09fb2b0e56fe.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1]

-- Cycle fingerprint 13e285cfe2d6db47ba55cbf94c79eca8d4f4178265b4ad9f410d39c55d57df29.
def localCycle00021 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 19 0, .triangle 25 2, .gapUpper 2 5]

-- Cycle fingerprint 13f33c0f38363b72f052c73052cc25c5c9e30ab699a15d0a88c35fa6de335fec.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 142f6625b360c29a6b0a0479afa7ab31d849a38c288722bd63ad847f4e8e8d21.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 14b82fb973f140e19922245f8d2feb4eecc3319ca3cfb3388fc61f1575a65678.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 158903999f7990c2ce967ce85e9c58c0c254b727b19e59b936b6c1a07cb6434a.
def localCycle00025 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 18825fe1c4e18cfe5a8007cd2253a26b04506ed510f84ec9bbf169ce2e8ba9aa.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 1cdc12df59f5ec70e95df14a6a61ab06ba61f483a8b56cff6453cbea37d52713.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![-3, 0, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint 1e029c70233ab7cde1764544ec61956c66d1046332907a06cb8af8b485ce2d01.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1fe93ea01ea0e6474ede696786c0b89801cf11ad0f129678e482523cdcc9d789.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 2007ee2f903abcba207f6fe4f3faa53f07694fabd80ffbd9ba98134f88e5beed.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 2052f118b84c97d8ea6ab55cf24e4c0f2594b0caf99218646fb646d0b3cd5c2b.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 20890f1fb9f0f0dbf865adaf8e5b3e68a2ed0e054d510e0c05a06c1973062739.
def localCycle00032 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00033 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 226155d7c180362c1e9788e940aabc09acea3fb82204b58ad656bf7177c9fe7a.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 23065613c3603aec1c44b6f137cce2d970b4e5c90ab3d238efa148eab8654b96.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4]
    constant := ![-1, 0, -2, 0, 0, 3, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2]

-- Cycle fingerprint 231262f4c1fcf5723d8f7b31672c2c356d814000964130564e2e125e4d0924de.
def localCycle00036 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 240de47ea48c581262c45579628fc8258c705ef38bb6945a975935311c4a694f.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00038 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 261bf811aa0df56d8f9fe482d2121c9e5950b2668d94cc44770a001eb6af36cb.
def localCycle00039 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 1 4, .triangle 19 1]

-- Cycle fingerprint 26911811eb3771af3b2417ba6c62a64c2a247301ded362e5f41d9affdc0ac6cf.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 26de5922f024482c18d38f12881065bae586345ec0385dad86ae5999f790b2b7.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 273bcf25ec29f5625804bb99b446008373590371664ced522b8f438b70ba9ba2.
def localCycle00043 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 288248ca73cf81170c3acad7cde94193670ced8f24b4b39ebf05f8a0de07efcc.
def localCycle00044 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 2a29636464bbb883da691ad5592bc4c9b16e2f55825429cb5c59019715d6e241.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 2b1a3202889fb47008b8ff86a7361dc2b3a236ec22f7eb629d8360c201825c56.
def localCycle00046 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2bbdafa30bc5eef8c95ed9be279a6cb8d267ec949f3fda9f1d79048ac78373ff.
def localCycle00047 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 4, .theta 3, .distance 1 3]
    constant := ![-2, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .gapUpper 4 6, .thetaNext 3, .corridorUpper 1 3]

-- Cycle fingerprint 2bcf93967e60d73ad97b597244717b6e170ed985796bcb401728562f06193e57.
def localCycle00048 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 2bf0617241657e084b772c9a3aad08a513c9ca78cb6b52a2130d7e670c9bfe84.
def localCycle00049 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 23 0]

-- Cycle fingerprint 2c3d8733aedca32718bacb50a682eefc52f528ca78532e84ad7c97b5233332cb.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2d18be0d3d5484ccfbb564e334f0f4775efc634a6367f1779e1497f8bad04533.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2d5056c93621918a9b06572646085e6b0d74f05337fece13bb054b10a13101c6.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 2dc767f5cebd8cca45ea42256b03ba907fb2fda095f32a62952a50ba558d53b3.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2e15cff8013f2f227fd11f80221ac528e93b3dc1ff40ce45a4ce73613c647bc3.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 304a580ad65c12c9378038179df725d2468b6a15e274800cfb0c6d0d5c51e66e.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3051904ed865f88664cd15a117b8e40857cd01028e0e9f86b906dbcb287026f3.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 311b6726b2c68cde171501f2cbd3d5e993efa99ac9d81e05134297b159894325.
def localCycle00057 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 3295a7a09004ae0284bf2f3e7ba9d09d65bed005921b2ca197a066994e7d1085.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 32dd8c83e9f39812af08f7f411fdac33c4e82898d593f367314b3068169406fe.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 35a6277855c7c950dd69693057ab3639ea252aadf0a958cc3dbd6848f9e43eb3.
def localCycle00060 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 36d3d2ec93a1f39ebead2ce90e1a82b2cf08a67498c71539cae35b75e1659f26.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![-3, 0, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 37563f5bff8fc689f26bc0dcf8d8973f3b3e247c80d7852f15ad9b5e157d93a9.
def localCycle00062 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 23 2, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 376d0d37c48c02a3850decf31e081a2388db1b46798d88dab2d3cac3102355c0.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-1, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 3a1093b69e7489632caa896c3635560225985fd2aa01c9ce6141a64c9b52f551.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00065 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3a4fc4710763e4350b20623d0e2e256681be05c1cf0b89d88e9bb1d83e60f61c.
def localCycle00066 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -1, 0, -1, -1, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 3fafd6280725cd3dfa3ebe32eb95e72ac0af7f1479e80a75cbc565327a3a1916.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .gapLower 3 1]

-- Cycle fingerprint 40104c85c1d689c63ae3289306bd9cae4d93fb9c7cbfd9838bf3cab434157b88.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4027453bcac4f345a3f79df57cd88bfbaa2e5843a4317e203c7e5fc9433f77a8.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 406d099413ada68b7b31a61eb056693e583fe93772564d019c55e1b21dc9da57.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, 0, 0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 34 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint 407afdd8a376a50848359ba505b9bb94e3b41ce64461d461be961158b7db646d.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .triangle 19 0, .triangle 25 0, .gapLower 3 1, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint 40f9cffc360f3e74f208c5ecb2c6fd4cc8aac5f33b669226e996b675afbaf9a6.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 43f82383057794832ebef93c5fb26be0842c9b823c6380a4d612b1120a99d2e2.
def localCycle00073 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3]
    constant := ![-1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.triangle 26 0, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 0]

-- Cycle fingerprint 44895357066980f36fde9005f7280c02c7485806704659c9010872dfc9f9f5be.
def localCycle00074 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 480e0c394b9eb1f3de08bfe9d3b3d5c41ca6e33cd4db0d2ac3461bf1cba83235.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 489acfdf238afeb443bf7c2086f57fc32eeaff9a5104334426197e500d3fac31.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, -2, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 19 0, .triangle 25 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0]

-- Cycle fingerprint 4a935e792adf5d1d46242a03185bdc34bdad51ae18184e7d09bed3e9039dbc00.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .gapLower 2 3, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 4bb6ffa9b14b6e6273aef60434d598d8c06c13cc535a935ef57c019846845ce2.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4d3c04042c10be7173537109765e15a394a6aef489c830e8609db91844fa780e.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 4e3455f54b088113e388fccb71b857ae3fec72fb5777b03a7531e0b30ede0531.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 4e611817b5d5c20cfd8816b50512462ee69b7d000954a2a3f18dd13c2fb97ace.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 3 0]

-- Cycle fingerprint 5060d1ee4e6f0b23b2cde9b3b6a2f6406059fa3cc592ee8e2239937ef119651e.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 5080d304008d3ac6e9d7325bae116c1c02a94665e9c20cc2f7896d81f229f98d.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .gapLower 1 2, .triangle 22 1, .triangle 28 0]

-- Cycle fingerprint 5194e5a1c819c71055ac6ebf27d09e77cb0ade5deee65955cdda51e4703700cc.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 51b578b169d77bd77e394a503bed1936cc55ca1a6fc1d0e043c364e6dfd3224f.
def localCycle00086 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 27 2, .gapUpper 2 5]

-- Cycle fingerprint 51e771639819cce04857887021d46f12821c1756f964fdf91541c95e45bb9fe1.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 28 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 29 1]

-- Cycle fingerprint 527c0a4f472c6da66bf99410c0f65564b7e329081941c7dc78ad21d2924c0b9a.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 529cfa3758e6ed52f35d05a7b4cd2a67c2c62f021fe7f5c2eee10a1bc979b6bb.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 537bca77ca200665947c0d91df4706a16a2c6d73ca64f1a288eda91f52a8cddf.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 2, .gapLower 1 2, .triangle 22 1]

-- Cycle fingerprint 5516b66a16e521fc46a45ae400827b4adf6a790cb9d965a53d3c5c6592f7ad9a.
def localCycle00091 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 557a9a3067873f7f87cd621cd54e1b717271f137991bbb6c80260eada977c630.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00093 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 562f3d7ae9bf618f25cb713230bc81f9d0bc0e6a7912377af36f2d563e46addc.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 2, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 56bac1e5418536e6ed8ab2aed7051e7ee32b8d5b22eff10d975f618bc7459ab9.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 58aa70a58bdf4666443b156970c82435fd2c825ba8d49f7e0f93fde1422c7625.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 59772f0b4d921709e0f92c6e5243b18dc8003067838595938860906ecc795ad2.
def localCycle00097 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 0, .triangle 27 2, .gapUpper 2 5]

-- Cycle fingerprint 5b653f314b8cdfdf5b7a14a2e4ade751829bdb6d18c2fe4fae6a4e80f5004a6e.
def localCycle00098 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00099 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5d4c2057678f3f9fa172c433ddae59ca5513b52bf04ec8fbcbf7d1230c504fa5.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 5d5dbb93138e3b57ee4d0d6f2b706078000e83799aef0aadf87f282b87c67f8f.
def localCycle00101 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5d812eacb3833fcb31e501d819ddf2ebbcff4fafaa7e20dc7fb693b5f9674978.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00103 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 605d71e2cd0dd8b75ffd899fb67281ded0bca34e769823cf977c2b9c1f60df45.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 6116df656d06fcc743012622b3b4d08ac91bbaf6ce3dc5dbc3b65ca04b9c1bae.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 20 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 61ebacee2fe9af5ade61403aa7b875ebf97208bdf2a11fc0de025cfbd59b0c70.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 61ff67ef57b650646801544653694efca7fd3f27771054ba187139b8b4a48cb2.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 6246ed20ef0893f816bf8a1e363db6c2a7bbb7ad401a917c743662f6573e32ca.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, 0, -1, 0, 0, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 625c64078baa7e3ad6beca1ec9a6ba17db127b313a012a5fdc7170d7661ed7ac.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 30 0]

-- Cycle fingerprint 634535ea76e28c04c68e4a4b66b11e367244771c2617d2ac6644a761f698c180.
def localCycle00111 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 646e00c23a8848cd65c87040ab5567d8484a645593bb2f1ef44c2e0833cd9058.
def localCycle00112 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 649d0528c36f9bf7251de5ff5ef29c00432e903780f9e54f3dc67a6dc1a8b805.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 22 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .triangle 23 2, .gapLower 1 2]

-- Cycle fingerprint 64dc4f0f60d4b930ed14e8ec2b47b44f80d9514a5e62a9c2f2101ce7b7c6d474.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00115 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 6617abc4477249de99325775e71a9605656f7116034f804042b49cb818caa4dd.
def localCycle00116 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 677af02f0369e15a6cb120a3a3d41f5c2d1faedd47f1c690176001e50e88f87c.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 67d03606e0f26909273e1d55805cd8ad73bc9bf503162c85601b796c52656989.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 68e96ea479279400328671e435d54e9088b3144a81c0cab8f774f04c1a7a7385.
def localCycle00119 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 26 2, .gapUpper 2 5, .triangle 15 2, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 694f94acbb1b08719163b26a51f733584e4dc275cf0b76f2109694cde7efdca2.
def localCycle00120 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 6c7a9053a33bb0ef040c4085ef4ed872c2ecff0b69840b7bcb5932581140c299.
def localCycle00121 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 6e8c5f99c6f77869148f214811408856f39a2ece2180d7b1e59c399e5a55c466.
def localCycle00122 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 2]

-- Cycle fingerprint 6f6463979d3e04665c6347d93bb980dba8599cea7325e09623b187ddadae7621.
def localCycle00123 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 6fdd979a52f1b5bcb658130c4c50de86e730d62719573700669b192b283091a9.
def localCycle00124 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 19 0, .triangle 25 2, .gapUpper 2 5]

-- Cycle fingerprint 71fbe89b22d9f51c33c26894e2ca9c1b1d0063d1951a60d6b24e99d455ee785a.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 721372d192b8675565d833bb3ffcfc6418c3b4ad1fe59d1ddcd93fd9bcac62b0.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 72553ed20e833d0b39af5c61c68f0f6064ea5282a7e9397852e588bfbbd533c8.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 728c92c0b0eb063b6f51a354165e23c68140ee9371e2ded02837476cdf460433.
def localCycle00128 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00130 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 76174a6fd7524be8ec8fbf5ff5d146737fe60f4f9b4dfd5bf8b15a09f8691fd4.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 76b24129dd07a00ba7bb0dcdee3999c2b0b809b4074eb162523e61e92a438dd3.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 783e2b4add81bcb2d13abf40f690ac662e5fef18a2cd1c57941f7f666c7df84b.
def localCycle00133 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 78725dc908b7da6786e24bd0542060bb6abffe307149ae15c7dedbaaecbae246.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .gapLower 1 2, .triangle 20 1, .triangle 26 0]

-- Cycle fingerprint 79e32f577f9b568fe5eb90e58819067fe1ab65dacb4cb0017c6d9baf5bdd8d15.
def localCycle00135 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![0, 0, 3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0]

-- Cycle fingerprint 79f29f3e8a619db4ab4f99639b571d4c2cdd3bff28c01e7b88e0ba9486e44dd9.
def localCycle00136 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 7de9fe481aa6220c5bc6ab3375d27c555fcf4646f57baabe18a5695104c78f2c.
def localCycle00137 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 6 0]

-- Cycle fingerprint 81135c0c8b2d4e17aee49ca1e6964146b551fe5baf5544fd362889b5c49388fa.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 81974a403129ad27af7c47d16310418185fe507689c8dfb159286184eb80a85c.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 84119cce138f8f85a8efe090b4c4574efe75fd77ec65e5166b5c24d2364333f8.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint 85741ce699735685ecee48139f49aa976103abffe4401542ed9b849cf5f8e441.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 87e97e712aac240ee57943338fd8d00fdb881f0912d75901c7954a6ec321ef52.
def localCycle00142 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 5, .gapUpper 3 6, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 8cae92ea386e342842511ce404b86cd642f2c341b44860e97810fd06b408496c.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 8e6548b32a7e00f2724ecf64702b94c255a336baaa3ccffabd3f30c5a3e8062a.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 20 1, .triangle 31 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8ee14a3e7ff4a911e1c984d617a9c12be72027072b7f293e571579ea72d247f5.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8f1b2375c20548a9ad190d2689065eba05f12f69d1b94f6708259ae162850f6d.
def localCycle00146 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2]
    constant := ![0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2]

-- Cycle fingerprint 8f3029d86541e2762f4a704cbc772f669f48b39f7736c631abb8d5f7b99f7446.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint 8f958e8c6f140c90fa731014669dfb9221c028aecfe61fb89448a32babc29194.
def localCycle00148 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 23 0]

-- Cycle fingerprint 9261f4635444a370eb8a09c137e910d5e34d349427606ce51443c628123900b6.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 930c483089ec2252e760ed56a360c9401aff85bb97707c037a348bc5ce18286d.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 96b1a0962619ad1883f29f0cfda842acba6539633c5d5e07fdbdcabfecc96311.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 98e1ece75689d298186a4024c2c2babcc33b9d713ac276fdc1794e953fd0cfb9.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 990a33dbdee11012ae241dbe8b9ce19e4b784cdbaa828aff6a074d4f7f8e1818.
def localCycle00153 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .gapLower 2 3, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 9913b836a5771a0c9a9940c1e90ee2535b123173e93017cc3547600d8d5e5894.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 3 4]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 24 2, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 9cd7fe19cf523929e8ca9e49d3375f9243d168b6f8a782cde9b8832b46578c82.
def localCycle00155 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true] }
  origin := ![.triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 29 2, .gapUpper 2 5]

-- Cycle fingerprint 9de7fa9a6d270e4cbfc654eaa00780b7cfadb7e6f04c809cc69a008e54ac9b0e.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 2, .triangle 2 0]

-- Cycle fingerprint a23d16404afef87b817464e44710b90c26d00d4f9ee04703c966896a05bcb20f.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint a285fb28fba0b1d4ffce8893f8a76389477919d1609a7c4a6dc126bdc0669bf1.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint a2eff47b36734f173eee0156d90208f98f6e7c5967a5708c2eedeccc715eb65a.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a3f041eb08b8937aa7b2c3f6dd21306b82c54ac33a72cf51ca2c8d941536cca3.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 4, .theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.triangle 34 0, .triangle 14 0, .gapLower 0 4, .gapLower 4 0, .thetaNext 3, .corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0]

-- Cycle fingerprint a3fd58977cc8bbb61526ba5da32b5549a852bccdd936d741d82c2ab183a1dccb.
def localCycle00161 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .triangle 5 0]

-- Cycle fingerprint a42e916cff90a41ac0a295042c06eefbc395b7d630d3093817dd5b28db44cced.
def localCycle00162 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-2, 0, 0, 2, -2]
    coefficient := ![-1, 0, 0, 1, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.gapUpper 3 6, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint a4aa11701ca64cd97fc33782c0c8bdd826223e85709c4afd3b467ab2f08cca85.
def localCycle00163 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint a4d206a04252ede336a89427325ecd08110b42f102d73c41af2d6b3bf9d74125.
def localCycle00164 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint a54b782b9cf4a9956c12ef283798793e316bd0156e7d5585367707380e84707c.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a72890de0f399119f1f48d552ec546c4a098b8fe9f3449997622b5d585b8c70c.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint a9e70f1ba65aca628afc4ff3c7688cbf3ff3d188c3e184933c275eedfce79c7f.
def localCycle00167 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint aad4ce51e31483ebae2cda51b9f3bc76ebe8e84c962848d0e4303d8fd5f975a0.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint ab45cdb011f47251381b73f165f8b44e90139f7f47fc666b3742a0945eb01777.
def localCycle00169 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 28 2, .gapUpper 2 5]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint ac9fafb5b287610b60b9d30e03e21f547743c40eba9b20ffbbdff997fbb1cc68.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint ad81186924ddbc960c38d915e75be491f90d21c84594de40af1c08bcfc3d8408.
def localCycle00173 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 3 5, .distance 2 5]
    constant := ![-1, 0, 0, -1, 0, 0, 2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 30 0, .gapLower 5 1, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 20 1, .triangle 26 2]

-- Cycle fingerprint ae9275507efd631f9e98e7aedcd3d02787f2d04fed7ad339cd8e19b87b313f7c.
def localCycle00174 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b120b8c51174234f0e78d8578060ae63a028f1b2dafc4ab26411dd7d28c29527.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 25 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint b1554373f8d14223fcfa325a700c3ad36a1c05dddef71aa5fa8476b4c5306112.
def localCycle00176 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 33 1]

-- Cycle fingerprint b3e2dc620f2760a21d18fc005e4c80b113f497e19516741e8de3f207dbc6096c.
def localCycle00177 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 15 1]

-- Cycle fingerprint b432804b4a29924b13e0498089b58fbd86a84910e76e670c19b32206caefa9b8.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b4dd15aedbb56dd576323977ab6c28ab33707136b5857ae9c1617b2754863f1a.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4]
    constant := ![-1, -1, 0, -1, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0]

-- Cycle fingerprint b60684e7f0dec2077b0140fe535361eb049bafacb2a4e2554ec0ac0f068b4be1.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint b6ef032a119df75ea7eb452f4a76c49a8edb5109bc33cc8e7130094256ccc45f.
def localCycle00181 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -1, 0, -1, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint b90faba7513d3d628101fa0943cb471acc68430c47e56acc2cca1bd074a86e7b.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint bbac6465abe83a3336836a3e419f3ca39d35e1e9eeef90f23cf1d3a16bf507f8.
def localCycle00183 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 2, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .triangle 7 1, .gapLower 2 0]

-- Cycle fingerprint bbbab754c8438e6aec2adbef9d406c299420a179d1cfe748efe3a716c4f05b60.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![0, 1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .gapLower 5 1, .gapLower 0 4, .triangle 2 1]

-- Cycle fingerprint bc81f0394b7042ca789ca3ad249cdd49428788f791a907fe8b2625d108c030f0.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4]
    constant := ![-1, 0, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 25 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 20 0, .triangle 31 1]

-- Cycle fingerprint bf4f646a0fb5750a5a59ecbdbea96c39298fb1b9951decd69607f46b0753cf77.
def localCycle00186 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint c197d619419a41b7fa517e627773280a56579a81ea36e2c9683ff1f42d8865ec.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint c23af404d4719fe1f62edfbf3f28f885de7321484ee207418960dafc7e015a49.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 25 0, .gapLower 3 1, .triangle 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c392e000da2c54379b4576a2e64d7138fd37d78c7e5c11ffd4639ea112c09775.
def localCycle00189 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint c4e966f01e44a61cd0909c860e95f074708f1569541bd72f6b3c62da7a8a8660.
def localCycle00190 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c5106bffb8c8220ca0a0284f86a56f7dff436c083f5829e1be584f44176ff3dc.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c53c1f0595bfc7e5a56d2cc99360f23b6033f814f60a24cc1e7f53fa9bcd8e57.
def localCycle00192 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 4, .distance 0 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 2, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.thetaUpper 4, .gapUpper 4 0, .triangle 2 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c58451f88e640a735868971ac5edb99cbfe2a508aa8ea115ea59acccd0d1ffda.
def localCycle00193 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c66bdfaf8f4775a293fc8369ad27dc329d9e47e01fb7b3fde1d61da18f00faa7.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 20 1, .triangle 26 0]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00195 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint c979e848d55dd83925d29c3e0630509ac7a732469f22e0cfdf41712442bc36e2.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint ce7a6d7002be177f3748f4ff4f23ce828038f25ba9b3a910013727096a1ebb1e.
def localCycle00197 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint cf0deebd060dbe7774ae7b3894a459ea806f02f617b57f30c1aeee987171e85c.
def localCycle00198 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0]

-- Cycle fingerprint cf1c52029177f9cf995d99b57850d4e11dab02c4e111bc1696a5b6adbf576b20.
def localCycle00199 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cf9a7ee9063ffa36f46681a2142b4c8ec16c05c700f41a8bfe3bf514d96a6d67.
def localCycle00200 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint d29349d8fe5a35cb8183d8f4e1ef72b6f27c9549a91c60c771706fda76823c91.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 25 0, .gapLower 3 1, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint d4447418a579d59cde84d4e5e7ff05b9b9c30462db05c3fc2e3a75301f8f0591.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d4bb3bf206a830cd71f8535a6ef736a20f0a08b33380c3613ff5ba9a08691d44.
def localCycle00203 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d5410b3b66fe88b1b7211626fdd21244995ba4346b25e93045b42c789436b219.
def localCycle00204 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d5f40763bb168e318e78b818383954500ffe3337ad609bf91b101a596794b4df.
def localCycle00205 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 2, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 2, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.thetaUpper 2, .gapUpper 2 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d62b5a17a3fa3d1d938e3e1b182a465043fd11e9ada8192967851edafcd5d212.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint d68d6d78304f955a62894676ba253a8d8c5b1419395e5b038825040658c593ec.
def localCycle00207 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint d7691b77a98be61841d5320906e4e6975c300a53bc9c5e7aa655b22049914016.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint d93851b556ac60e2b56706eeb0adf8dcb94a58559f45d73e901c2d62a2e5005a.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint dbea66e0cfe3c2cdefca935e2638cd5aa0fd2289d9427ebe568da15514961e8b.
def localCycle00210 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 20 0, .triangle 26 2, .gapUpper 2 5]

-- Cycle fingerprint dc1c3118e1872cb9e78e1ccb9a8b913594d8eb92246d7c709c3da072cf60f515.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .gapLower 0 1]

-- Cycle fingerprint dc55fb13b13cb2c8a602500aeaa770f458849881b0a95fcf863c605d9f42207f.
def localCycle00212 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint de8e04ea592ca49937eaa0e0cad5a3fdf942d18dacba4f35a4bfc6475e970f42.
def localCycle00213 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 2, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint df30ab2612525d319ab5872ba35ae8186ea20fb93b9d0810fe85d42bc2809fc5.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 2, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint e55bbffb275efb82d5e5a9b0cba97321167410be9710db77d8f02279968fc697.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint e60ec808641854d017dfb312f78f608df29cddc5dcf0ec41c8c3e045ba1a459c.
def localCycle00216 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e633f2abf4933741cc1b4b712671d1d11596d08d2e7e21ead78f1d2cb3dc05f9.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint ea1d3007b9da6a4998ab61cc0e14719dab0a9ff9e14376034b3508e8e1ea1546.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ef1375e6bdee8e410acf2bf1525012324119adfb6b27ad7c44d316e4d3d812cd.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint f24fe31141af338b46bda55b1e29d18fdf9e417218d8a03783305d51638f3a60.
def localCycle00220 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 26 0, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2]

-- Cycle fingerprint f318b5eec8a0bfdb8e02869f8589fbdf0273817345c25baa6185da75f8e4fb4b.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f4b528fd729607afd43c25330bafd5c791871523cbc8f0eda4847a7766d411c6.
def localCycle00222 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 20 0, .triangle 26 2, .gapUpper 2 5]

-- Cycle fingerprint f636db07bef414c48d463ab6ef338815044ebb0d9b26eccf4fcbf3ad62694fe0.
def localCycle00223 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint f722cf157794c80e22eaa77583ee96315a68997cb5fca7387cb187627137d443.
def localCycle00224 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint f916cc537e4bca96fac2ab6c97a7fad1bdb2d3abeef208ecded2ac621ecb7b35.
def localCycle00225 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f93f4bae1cae67952bb322acb904a6a370f1bc97e5b4a18e1d2bbd7bf648a630.
def localCycle00226 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4]
    constant := ![0, 0, -2, 0, 0, 3, -2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0]

-- Cycle fingerprint f999fe45e9a4679f2754c6a808dfcf40189a14130bb73177ccaa9b4841a888fc.
def localCycle00227 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint f9d0c195b1235283f0f9fe7abbaa4257832f9f7d2cbeb8ad2b45bf210abdbfe0.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fa6ff66e780d1dc32f8cff4ab785927ab0256466ba3ae0dd4c00b70e5f1a8982.
def localCycle00229 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 27 2, .gapUpper 2 5, .triangle 15 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint ffea61a06f15b810d616f97cffbaa096a98b0a7d7a607b7f1317ff691d15f793.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 2 0]

def library : Library := fun id => if id < 115 then (if id < 57 then (if id < 28 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 24 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)))))) else (if id < 42 then (if id < 35 then (if id < 31 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))) else (if id < 49 then (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)))) else (if id < 53 then (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))))))) else (if id < 86 then (if id < 71 then (if id < 64 then (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)))) else (if id < 67 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))))) else (if id < 78 then (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))))) else (if id < 100 then (if id < 93 then (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))) else (if id < 96 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))))) else (if id < 107 then (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))))))) else (if id < 173 then (if id < 144 then (if id < 129 then (if id < 122 then (if id < 118 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))) else (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))) else (if id < 136 then (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)))) else (if id < 140 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)))))) else (if id < 158 then (if id < 151 then (if id < 147 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))) else (if id < 165 then (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 169 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))))) else (if id < 202 then (if id < 187 then (if id < 180 then (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 185 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))))) else (if id < 194 then (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))) else (if id < 198 then (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))))) else (if id < 216 then (if id < 209 then (if id < 205 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none))) else (if id < 207 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)))) else (if id < 212 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))) else (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))))) else (if id < 223 then (if id < 219 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))) else (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)))) else (if id < 227 then (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))) else (if id < 229 then (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 1, 6], ![0, 2, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 179 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 768)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 4, 1, 6], ![0, 2, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 207 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 769)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 1, 6], ![0, 5, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 199 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 770)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 1, 6], ![0, 5, 2, 3, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 133 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 771)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 1, 6], ![0, 3, 2, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 772)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 1, 6], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 212 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 773)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![0, 4, 5, 2, 1, 6], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 200 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 774)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 1, 6], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 190 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 775)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 51 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 776)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 144 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 777)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 11 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 778)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 1, 6, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 138 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 779)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 1, 4]], proof := .low (![192, 99, 130, 27, 57, 222, 184, 65, 156, 141, 119, 210, 115, 182, 81, 119, 210, 63, 13, 154, 210, 106, 30, 210, 189, 210, 173, 185]) }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 780)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 28 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 781)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 216 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 782)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .low (![176, 170, 33, 228, 92, 177, 93, 129, 17, 221, 151, 142, 29, 159, 107, 95, 142, 139, 150, 166, 142, 230, 22, 142, 25, 142, 20, 162]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 783)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 8 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 784)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 216 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 785)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .low (![176, 105, 195, 98, 92, 177, 93, 76, 41, 18, 151, 142, 29, 75, 48, 95, 142, 172, 5, 9, 142, 9, 22, 142, 25, 142, 20, 162]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 786)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 1, 6, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 171 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 787)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 1, 6, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 202 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 788)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 102 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 789)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 5, 1], ![0, 3, 2, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 80 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 790)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 3 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 791)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .low (![205, 99, 130, 38, 136, 177, 93, 65, 7, 145, 123, 35, 115, 182, 81, 54, 197, 187, 6, 54, 197, 106, 110, 217, 189, 108, 219, 209]) }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 792)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 1, 6, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 24 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 793)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![0, 4, 6, 5, 2, 1], ![0, 3, 2, 1, 6, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 55 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 794)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 6, 1, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 50 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 795)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 6, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 50 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 796)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 4, 5, 1], ![0, 2, 6, 3, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 155 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 797)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 50 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 798)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 2, 6, 3, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 89 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 799)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 6, 2, 3, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 120 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 800)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 5, 1], ![0, 6, 2, 3, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 112 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 801)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 6, 1, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 34 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 802)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 6, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 202 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 803)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 132 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 804)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 5, 1], ![0, 3, 2, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 15 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 805)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![0, 4, 6, 2, 5, 1], ![0, 3, 6, 2, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 153 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 806)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![0, 6, 4, 2, 5, 1], ![0, 6, 3, 2, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 143 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 807)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 64 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 808)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 31 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 809)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 6, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 36 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 810)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![0, 4, 6, 5, 2, 1], ![0, 3, 2, 6, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 223 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 811)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 83 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 812)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 4, 6, 5, 2, 1], ![0, 3, 6, 2, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 83 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 813)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 6, 4, 5, 2, 1], ![0, 6, 3, 2, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 101 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 814)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 179 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 815)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 4, 6, 1], ![0, 2, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 204 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 816)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![0, 5, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .low (![188, 225, 43, 122, 128, 97, 201, 46, 74, 42, 229, 86, 115, 74, 196, 229, 86, 87, 194, 74, 86, 74, 227, 86, 100, 86, 16, 175]) }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 817)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![0, 5, 2, 3, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 163 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 818)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 116 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 819)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 216 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 820)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 78 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 821)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 165 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 822)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 212 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 823)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 191 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 824)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 32 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 825)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 5, 6, 1], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 161 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 826)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 4, 6, 1], ![0, 2, 5, 3, 6, 1], ![0, 2, 4, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 152 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 827)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 6, 4, 1], ![0, 2, 5, 6, 3, 1], ![0, 2, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 0 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 828)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 5, 6, 1], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 220 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 829)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![0, 5, 2, 3, 6, 1], ![0, 4, 2, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 114 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 830)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 2, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 218 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 831)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .low (![67, 225, 103, 61, 39, 124, 71, 46, 82, 158, 47, 21, 115, 131, 56, 47, 21, 70, 134, 214, 21, 62, 168, 21, 60, 21, 47, 77]) }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 832)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 5, 6, 1], ![0, 3, 2, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 111 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 833)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![0, 5, 2, 3, 6, 1], ![0, 4, 3, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 125 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 834)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 3, 2, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 4 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 835)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 5, 2, 6, 1], ![0, 3, 4, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 45 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 836)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![0, 5, 3, 2, 6, 1], ![0, 4, 3, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 53 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 837)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 3, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 167 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 838)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 5, 6, 1], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .low (![181, 225, 103, 224, 49, 177, 93, 46, 82, 203, 109, 226, 115, 131, 56, 148, 118, 140, 84, 90, 113, 62, 88, 94, 60, 117, 211, 19]) }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 839)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 5, 2, 6, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 45 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 840)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![0, 5, 3, 2, 6, 1], ![0, 4, 3, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 52 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 841)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 69 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 842)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 5, 6, 2, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 59 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 843)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![0, 5, 3, 6, 2, 1], ![0, 4, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 91 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 844)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![0, 5, 6, 3, 2, 1], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 174 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 845)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 5, 6, 1], ![0, 2, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 157 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 846)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 6, 1], ![0, 2, 3, 6, 5, 1], ![0, 2, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 96 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 847)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 6, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 198 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 848)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 4, 5, 1], ![0, 2, 6, 3, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 206 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 849)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 4, 6, 1], ![0, 2, 5, 3, 6, 1], ![0, 2, 4, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 72 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 850)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 6, 4, 1], ![0, 2, 5, 6, 3, 1], ![0, 2, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 186 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 851)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 5, 4, 1], ![0, 2, 5, 6, 3, 1], ![0, 2, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 208 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 852)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 5, 4, 1], ![0, 2, 6, 5, 3, 1], ![0, 2, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 14 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 853)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 3, 4, 1]], proof := .tail 127 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 854)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 2, 6, 3, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 40 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 855)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 5, 4, 1], ![0, 2, 6, 5, 3, 1], ![0, 6, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 169 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 856)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 6, 2, 3, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 213 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 857)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 5, 4, 1], ![0, 6, 2, 5, 3, 1], ![0, 6, 2, 4, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 215 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 858)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 4, 6, 1], ![0, 5, 2, 3, 6, 1], ![0, 4, 2, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 186 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 859)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 2, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 218 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 860)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 6, 5, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 2, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 79 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 861)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 186 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 862)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 104 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 863)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 58 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 864)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![0, 6, 5, 2, 3, 1], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 160 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 865)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 5, 1], ![0, 6, 2, 3, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 85 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 866)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 5, 4, 1], ![0, 6, 2, 5, 3, 1], ![0, 6, 2, 4, 3, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 215 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 867)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 23 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 868)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![0, 6, 5, 2, 3, 1], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 44 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 869)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 4, 6, 1], ![0, 5, 2, 3, 6, 1], ![0, 4, 3, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 146 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 870)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 4, 1], ![0, 5, 2, 6, 3, 1], ![0, 4, 3, 2, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 4 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 871)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 3, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 12 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 872)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 69 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 873)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 26 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 874)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![0, 5, 6, 2, 3, 1], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 1 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 875)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![0, 6, 5, 2, 3, 1], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 183 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 876)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 5, 6, 1], ![0, 2, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 68 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 877)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 6, 1], ![0, 3, 2, 6, 5, 1], ![0, 2, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 180 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 878)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 6, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 126 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 879)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 3, 4, 1]], proof := .tail 66 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 880)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 5, 1], ![0, 3, 2, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 193 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 881)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![0, 4, 6, 2, 5, 1], ![0, 3, 6, 2, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 178 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 882)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![0, 6, 4, 2, 5, 1], ![0, 6, 3, 2, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 149 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 883)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 5, 6, 1], ![0, 3, 2, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 137 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 884)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 2, 6, 5, 1], ![0, 3, 2, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 37 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 885)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 4, 5, 2, 6, 1], ![0, 3, 5, 2, 6, 1], ![0, 3, 4, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 135 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 886)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![0, 5, 4, 2, 6, 1], ![0, 5, 3, 2, 6, 1], ![0, 4, 3, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 121 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 887)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 5, 6, 1], ![0, 3, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 137 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 888)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 6, 5, 1], ![0, 3, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 10 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 889)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 2, 6, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 164 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 890)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![0, 4, 6, 5, 2, 1], ![0, 3, 2, 6, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 73 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 891)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 6, 2, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 178 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 892)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 4, 6, 5, 2, 1], ![0, 3, 6, 2, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 178 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 893)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![0, 6, 4, 5, 2, 1], ![0, 6, 3, 2, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 147 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 894)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 5, 2, 6, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 135 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 895)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (768 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 768 ≤ id.val) (hhigh : id.val < 896) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 768)) = true := by
  let j : Fin 128 := ⟨id.val - 768, by omega⟩
  have hsum : 768 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (768 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard006
