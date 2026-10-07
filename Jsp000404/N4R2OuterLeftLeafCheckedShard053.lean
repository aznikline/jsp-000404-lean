import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard053
open N4R2OuterLeftReplay

-- Cycle fingerprint 0757cebba9acdc8def455ec375e60d025abac4d38f4f5c8e45b3d09df6c1fb15.
def localCycle00000 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 07630a9256b8ab465a8c7f2be7fd77b285398969237c62ce9fce070f13636b20.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 0767da3a35232a7b4aba5c5346c548d5d7230e347a3e278333a47fe7fa539018.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint 07e809f3f4d5790e1da8ce5f39c9adde9c0a610e28a417fdc0ff02554064943e.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00004 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 09b19bd7d68ab68aeb9d8466cab00bd7246ece201fec9496e375b4c7df668d91.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 0]

-- Cycle fingerprint 0c8898b1ce092a8912e24c88453e88cc3a680cceb17e5aee3b76dbbfe02261c6.
def localCycle00006 : Cycle where
  length := 13
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 0f87001adf4326208981a4fe043729283fab5678a4909bb15378f78eb762efa9.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 108eb2f08ade1798a98f3713952a119210b6ee76553dab70b49760182f66411e.
def localCycle00008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-2, 0, 0, 2, 0]
    coefficient := ![-1, 0, 0, 1, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.gapUpper 3 6, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 11a42e1bcec28eb7cedeab220bc36516a802d3d4510f121d451aefa03582e149.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 20 2, .triangle 24 0]

-- Cycle fingerprint 124dc960ecaa01029a88d088dfba53cf4d9e8b803d565382ec84934e2d7751b7.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 12d4e056473b37f3bf0a10ec2fba7fdb71379d667303e3429a79afbbe461499a.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 12f9676d174bcafe0822280321522a532747e541f007812064d7c8c8419a5a61.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 22 1]

-- Cycle fingerprint 13362af5c001495e2448a492f16de03ffa7cdf14926dedbbb0c5bc7e6844f90c.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 13f33c0f38363b72f052c73052cc25c5c9e30ab699a15d0a88c35fa6de335fec.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 14fd425d75179ddc91b6e1e2bfe648540a16855ef551341ce8117bddcc48b595.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.triangle 30 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 20 2, .triangle 24 0]

-- Cycle fingerprint 158903999f7990c2ce967ce85e9c58c0c254b727b19e59b936b6c1a07cb6434a.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 18381759650ccd23930ecc0c2fb9fb823306e509a21af757e6ed76eda3c21de2.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, -1, 3, -3, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 11 2, .triangle 13 1]

-- Cycle fingerprint 1a37a7b8d5989b6c6d36fe2397c31a7514e7a0f7feee427e72e032796f6055bd.
def localCycle00018 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 1bcfa9cff7c5074e1d0b908fe669fe4be1c7cc093a7a350cf0ed2266f600d547.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 34 1, .triangle 28 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 23 0]

-- Cycle fingerprint 1cefac5885c676edf66e854fa19377780e800ad826974ee75fa998a7ae4ab667.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 24 0]

-- Cycle fingerprint 1f63413a13adec80c10f20e1690397f1fdc8484be8959dda75cad33d954ed600.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, 0, 0, -1, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 209b7bf1ed166aa7e909533f0a3c25626569aaf6be0a0c3a43d70338a2a0e2f4.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 20e91ba97e64baae116b70c47f3cb7b3616a9685d72ba3e28785de726a2096f7.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00024 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 2404085c80ad191177896776153843d4f380de2c1c0d5b52f1737af7dcf0dbea.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4]
    constant := ![-1, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 12 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 2 2]

-- Cycle fingerprint 240de47ea48c581262c45579628fc8258c705ef38bb6945a975935311c4a694f.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 247628e2168bd50a40e71b28ce19efec297b9028d429223593c7284fc7ad39ca.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00028 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 26e41729c90e2e928a22d487c5543d92086088a0669902f6fed2e788eb8277e7.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 27256bc11ea4eb0a6a660d5ef5b9081a84a7b3dc99c4ae183f38279075361e0d.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 13 1]

-- Cycle fingerprint 273bcf25ec29f5625804bb99b446008373590371664ced522b8f438b70ba9ba2.
def localCycle00032 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 2957f70ffb2f4418d3cc3738086b9be4aa8d11d4bc62af3c6b8a36240c40838c.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 2a154da14314ad77d12f73d4da6a515f9a0b6c1115b465c3f6bdbe0c2ca287a7.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 2a8c67e728c9e878d2bcb1cd91b4b20bac1f024862dee6a495dae9aef22eb034.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 2b1a3202889fb47008b8ff86a7361dc2b3a236ec22f7eb629d8360c201825c56.
def localCycle00036 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2ba6b65fbbd7e38adefb87662ec7ac0a8e1ffcb0fdc915a002d6c5ad15327ce7.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 2bcf93967e60d73ad97b597244717b6e170ed985796bcb401728562f06193e57.
def localCycle00038 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 2bf0617241657e084b772c9a3aad08a513c9ca78cb6b52a2130d7e670c9bfe84.
def localCycle00039 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 23 0]

-- Cycle fingerprint 2cffd3b91420df5bfd8b9e8de0b40929fe054f6b77abc891d852d24b522e7559.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 1 3]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 1 3]

-- Cycle fingerprint 2dc767f5cebd8cca45ea42256b03ba907fb2fda095f32a62952a50ba558d53b3.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 3051904ed865f88664cd15a117b8e40857cd01028e0e9f86b906dbcb287026f3.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 3090c57687515c1c88073bb80e64227c5628abcecf37165c7f8ec75974af6da1.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 32e15e3230745da6cba2915ab6971351fc19ca4d8a7c526f04c547ccba36e8c4.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 36bb9f417caea9251f1e2f8c90e3b703d3dd16bd0f2394a189d028398fa1f2b1.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 372051be226812c615587d193f8945c30c947dd653546575c7c50898678e057d.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 13 1, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint 38746791f7f7213b6fb12c92ca28d0fec15e11d2ebdb7f96ca83f14bd7055235.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 387b867b14c8ab21b0aeb10ab1188766bd2d0a76f99ec414847993bded7d0c4e.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00049 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3af8574a9f780b08407fee09a50fe113aa0a22c05d34564775f21874b3e472be.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 0 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![-1, 0, -1, 0, -1, 0, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true, true, true, true, false, false] }
  origin := ![.triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 4, .triangle 1 0, .triangle 4 2, .gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 3ecb9b4b9c4a0e7ed1eeb186cd60e386fd6df089168d02b0ebfccc3e1856dd49.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 3efe0e5ec6eb7c28778a059ae0ba842828c440df148e3f2160b9cce5619e7dff.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 24 1, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 3f2265c054a12abca210ce423bb02f9599d36063213476d09d31a08b4b50b635.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 42a09817590ba47f05bffea1abce7fdcc912ff621816c5b13340fb3b05cfcb4a.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2]

-- Cycle fingerprint 431ed06b504a22320eaca6c9107a4cc5cc39d42caa47152ec9d8de4dfcda9d5c.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 440af51a6ae0e552f35d52c8789b62c0d613cf16058c993839777a1f19400515.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, -1, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 12 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 13 1]

-- Cycle fingerprint 443563070970df43959f2e926746a3c9f5f722341af3b2bf27803e37e676bd41.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4470b638c8e3b4b3e786b670ed971329e258aebc2999ae80c087eac2312f7bc4.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 14 0, .gapLower 0 2, .triangle 2 1, .gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 20 2, .triangle 24 0]

-- Cycle fingerprint 44895357066980f36fde9005f7280c02c7485806704659c9010872dfc9f9f5be.
def localCycle00059 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 45157a4f1288c9bbb58b27f68986c7710f4e3817b74cf880c107a0d2adc3cfdb.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 45229ca0910521d6f3dda67fe10f9f10c33efaf6dd209e8b23c26e8b5254b038.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 45697806ab390b2e4da3db53bb0649cd09e1f0a6649dc528ea32ad1c04a7fb87.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 6 4, .gapLower 1 3, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0]

-- Cycle fingerprint 46234bafecdb42b8feeb7565823a0ebfd089333824c0a674dfb5886c20b4ebac.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4]
    constant := ![-1, 3, 0, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0]

-- Cycle fingerprint 477ce304bb2c35d3613c6d671daccad3b5dbff87719aece56e3c971ccf0732f9.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 23 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 4784dd9fd27f15314ac0c71007bccb30aa70db9b7f2412c80ed81a5785b02a9c.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 480e0c394b9eb1f3de08bfe9d3b3d5c41ca6e33cd4db0d2ac3461bf1cba83235.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 4abb10cfa660b6386dbdf7d0e843ae49bd84b415fba44705fb4a519ea40eebe5.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4aeaf14f40de12c99ca4492c5a5d7c141a504c03c63a5b50ca537f9db4a7d28c.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 4d6b8adb88a7d1736e9fcc870996e5936fbd18b054328058d95b3f2c57ae006f.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 9 2, .triangle 13 0]

-- Cycle fingerprint 4df527d58538c86edfc33b652ff6899f08141fcc951ee8d40f2cb5ea93680667.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 4e3455f54b088113e388fccb71b857ae3fec72fb5777b03a7531e0b30ede0531.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 5080d304008d3ac6e9d7325bae116c1c02a94665e9c20cc2f7896d81f229f98d.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .gapLower 1 2, .triangle 22 1, .triangle 28 0]

-- Cycle fingerprint 511b3910e065d92dfd9480cdc993ffb9307889249b250bc8100ffc250ff3a742.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 527c0a4f472c6da66bf99410c0f65564b7e329081941c7dc78ad21d2924c0b9a.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 537bca77ca200665947c0d91df4706a16a2c6d73ca64f1a288eda91f52a8cddf.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 2, .gapLower 1 2, .triangle 22 1]

-- Cycle fingerprint 557a9a3067873f7f87cd621cd54e1b717271f137991bbb6c80260eada977c630.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 562f3d7ae9bf618f25cb713230bc81f9d0bc0e6a7912377af36f2d563e46addc.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 2, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 56bac1e5418536e6ed8ab2aed7051e7ee32b8d5b22eff10d975f618bc7459ab9.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 56cb0b2f031adf8e9ffe07921d9eb8936943638c28710327780e52510a25f9c4.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4]
    constant := ![-1, -1, -1, 3, -2, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 11 2, .triangle 13 1]

-- Cycle fingerprint 57e1b0fcdcc13646feaabfaa4cec43cc3c38c276014cdc81c2e95e0a8d7a9026.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 585d4aa708d3aa98fe60da4ef555ba89ee102684cf491a69790aebc98b5cd24a.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 59f2d5ff0a53754a0a93d65d2ea7d82bf5f26cbd9ef63e11a95acf5740ba29eb.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .distance 0 6, .theta 6, .theta 5]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, -1, 0]
    strict := ![true, false, false, false, false, false, false, true, true, true] }
  origin := ![.thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3, .triangle 0 0, .triangle 4 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 5a07389c5bd13a174dbe4342c56c30c2b7cd533b8c5fbcdee93c558e8dfde314.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 5b653f314b8cdfdf5b7a14a2e4ade751829bdb6d18c2fe4fae6a4e80f5004a6e.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 5bf5c2172996a684fa822f32ec1b9a474377806fc9c4275e24253f0cf24804bc.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5dfa75eb45ce2f5d3535ec1653c6195e09088e6bff0a985fb24a49bd5e466643.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 5f8fa55adfc8c31f8c847d05a47c21f76eb35ba1909e946cee03fb86db0e2479.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00091 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 6116df656d06fcc743012622b3b4d08ac91bbaf6ce3dc5dbc3b65ca04b9c1bae.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 20 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 61ebacee2fe9af5ade61403aa7b875ebf97208bdf2a11fc0de025cfbd59b0c70.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 622ed83485d123dec98ae2d0416cc2df740dbddf38025a2c3c7b931aa959a041.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 649d0528c36f9bf7251de5ff5ef29c00432e903780f9e54f3dc67a6dc1a8b805.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 22 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 2, .triangle 23 2, .gapLower 1 2]

-- Cycle fingerprint 65d910d3e6f51af6a275f32a4582daeeb1dcde0b97a14fdb31ac1078109648b6.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00098 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 661ca9878b8dab4ec8635a4c780bfd6a4bafa28304f363cf0a3ac70ff8482be3.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 677af02f0369e15a6cb120a3a3d41f5c2d1faedd47f1c690176001e50e88f87c.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 67d03606e0f26909273e1d55805cd8ad73bc9bf503162c85601b796c52656989.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 68f93f3d2eb0e1f8c0d1b2d3fc6aa5cb14e199bfc30792301895ac638eb334bb.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 694f94acbb1b08719163b26a51f733584e4dc275cf0b76f2109694cde7efdca2.
def localCycle00103 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 6bb78a44d2bb469d576dcc19587589add3ea314900c204e0087da9aad578afb0.
def localCycle00104 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 0, .triangle 0 0, .triangle 4 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 6e8c5f99c6f77869148f214811408856f39a2ece2180d7b1e59c399e5a55c466.
def localCycle00105 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 2]

-- Cycle fingerprint 6e9878fb437b0ed50d4514c45ff6fdadb2724915447c7a3254eef7303f1e5814.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 12 0, .triangle 2 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 718959a11634e8950411595d3e50624f7fd4a1ce99c631a9724317a151c4d0bc.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, 0, -1, -1, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 7297674b2ccf472644fc038da50c1279b0ceb4602b7a78c45d85831513a450b3.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 28 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 19 2, .triangle 23 0]

-- Cycle fingerprint 7304814d12a418ba6027a3c19a4eca864d1576116b0c3988fdced0a8a21d59f4.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00111 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 76174a6fd7524be8ec8fbf5ff5d146737fe60f4f9b4dfd5bf8b15a09f8691fd4.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 79141ddd2445ff0e6564b38811a6ab550eea50a9286ca8ede4c715f959b493f2.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 9 2, .triangle 13 0]

-- Cycle fingerprint 794623e23f7876d2cea9b398baec81a95af9e03fc49512ce49b7533ca585e5b6.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 79bacc2c7797dafac7793e1bfa791fd6b12d64c47a7bd111e49d40b45c94762b.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 79f2a60f6bd6f21695c836dfcab6b379735fdf9d5dd4fb5aa6e705053295593b.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 23 2, .gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 7a5c39c3dd6aef6fe51c65626ee4e4f9f13eb0f1d89dc8c3166e5bc9ef6536d6.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7c928a678d942fab374b190e9f57de79c60178b69224ee20a2ba7b8a6310559a.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 34 1, .triangle 28 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 19 2, .triangle 23 0]

-- Cycle fingerprint 7dc0cd6898b2cef28f3adc1162746ab143557e5393ec8e61a7d0f222a2462abb.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![0, 2, -2, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 7e72ad9982621a0994f990db5b7ea9ac8acc80fd478546b617d1ee68ad026d04.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 8106247e45a19eb01614307cfaca2b14fb5c613268f69ef32aa3bb637f426138.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 815f9fdcb08cea219b67f6703e8019ef83704da8ce84ef3ff1cbfc9dffe5c104.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 842ef95e845982345987bc66f22c45c3f411356519bdc2d7bd688502a13e8aa2.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 8477d54cddaeaec9dbd299349eaf1eaab259161684c6c46cb8adabdd684907bf.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5]
    constant := ![-1, 0, -1, -1, 0, 0, 0, -1, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0]

-- Cycle fingerprint 87ae5543fe118add23f095338e63cf4329cfe6746971db89110cd7af0abbde65.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 87e97e712aac240ee57943338fd8d00fdb881f0912d75901c7954a6ec321ef52.
def localCycle00126 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 5, .gapUpper 3 6, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 8994dd04b9277797d3816f309a588c1d00ddf0f91e3d4be1c630793e348c98ed.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, 0, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 8bc2aac716900fdf3944a75d678a9ba1aa557d74ecb605765efeb3d8f93e66b1.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8d25f37777f7eebc82af7f47687ce1b076e6b48a128b43ecee31d5bb9fca0885.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 8dc32acbdac1c1410dbf8dd9198733f86a4b16945e73b50daf619dd911dae7fb.
def localCycle00130 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 3]

-- Cycle fingerprint 8ee14a3e7ff4a911e1c984d617a9c12be72027072b7f293e571579ea72d247f5.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8f958e8c6f140c90fa731014669dfb9221c028aecfe61fb89448a32babc29194.
def localCycle00132 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 23 0]

-- Cycle fingerprint 8fe5883b885b8c5244dfc7ab9c035c4ac7ce19db8a185e8334c7cb04d3434066.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 9089fe31e3200687b39de97ec4ea764a240a38b2f1942251e816c63ba6971e54.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 920b9e94e532f7da9ceb957d37e7c1cc5833db8bc6701a9e4293d1eaa8e36753.
def localCycle00135 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 9267a38b6f8c06635f7737e0cc056d9843670f087f99b48bdbacf534dea03ea5.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 926fe6d8689db9e8b5ec74209c68f21e418a667865146304e5bd2c2aa399b6d5.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 930c483089ec2252e760ed56a360c9401aff85bb97707c037a348bc5ce18286d.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 938721c4c4169e22f806348777effc4e17bea00acbb3d3963d6140d1e684e116.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 94f37c65de752457846f4175d51b77323e0bca296a9d0dce866c83ed9dd37112.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 95a31b83bcc4d7bce79293f2700f0255146aaf33ed7900c7ed63f5f252f5492a.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 9634a01aafdc59ce1170f92c24276a83f79a1f1dc012c10e1cbb71553f1c7886.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 96523e1e77b86201bbb26e30e702b68010b580759e58317e1ca4f9cb52fff2d6.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 0, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1, .triangle 22 0, .triangle 31 0]

-- Cycle fingerprint 981a8875b478556456f104b95ed590fe721b8cdd7266f3c55d54f1bdeea3d708.
def localCycle00144 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 9f79b9e86e67dd454889648d015c8fe6461ce2a8a20e3a3bf40f253fbda7a333.
def localCycle00145 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a025abaf1bd4c2a4c506d6ceee610daeef9c7b74dab660ae39f3c35c8fa4f329.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a06539730ff3a994ee2e7cd30382f784ce30f643575806b9b7f15a592f632667.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a1ba0101e24d47167374985fbc553e578df4e23d55bbb78de7ac16fc3e0c1d9e.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a26b4811d0add84c90cd58e04100a7f203f4873a2d5f3bd71cd8ffc5cb0475d1.
def localCycle00149 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a2eff47b36734f173eee0156d90208f98f6e7c5967a5708c2eedeccc715eb65a.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a332afe9e39879c97f3c4528eb73288f62b94a11b24f5bd25115f7226264841b.
def localCycle00151 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a3634602ce2f3b4d39050a6a8db01282b7deace5e72892a122ffbd4e0b810d46.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a4304c285be01dec1327cc9aacb62e34d7e7071e848418a088376688888e2568.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a64ed551bebb47ad45d7309a4a30e87e00ae19b231e143e5ea7e17c07146300b.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -1, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 23 1, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint a72890de0f399119f1f48d552ec546c4a098b8fe9f3449997622b5d585b8c70c.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint a76343718f6f59784f2b173ab924c615c77c41c192084aa290e320fc029b33f5.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint a837fbf9e5ad206fc0f00fb3ea308162b80d0d272a251a7ef1614ccfe9739bbc.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint af8902314d891d24fde16fdc0f17b406fbfa9ab0b22b76b332dd8ef6ca01599e.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-3, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint b0ae52af2b55199676c41a28eb3cf87cda25071ecbbbb5c4817f237b7644bebc.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0]

-- Cycle fingerprint b183588a6672be507514b8a209a91ec03e693be963f0c604261a3ad6c840f855.
def localCycle00162 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 0, 0, -1, -1, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .gapLower 1 3]

-- Cycle fingerprint b432804b4a29924b13e0498089b58fbd86a84910e76e670c19b32206caefa9b8.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b6beb625752aa19c63e61b3551f0a23c9b611c706773d30a1e6bbdd8a6b12676.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b90faba7513d3d628101fa0943cb471acc68430c47e56acc2cca1bd074a86e7b.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint ba4b2dfab8653b3adc5ea729a45732d1089dbb94382fc55ed37378e97fed4a17.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .triangle 28 1, .corridorLower 2 4]

-- Cycle fingerprint bb9c201c02145bded19011e66336e1bec0675ccaabb70bc0fae1d170c13a6b67.
def localCycle00167 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-2, 0, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 1, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint be1f73c526ef8a91f6a7adb9ce9f9845c660c7e4ee28a2972a54a57a8efe8c43.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint be8ac4a57826d013ce514e5363feb9805f6c4427a826baf6e9c76ef3b7b2cb7f.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c18f0f7083e194373224a931c932bad1d60faf3ad33dc03f42fcd80ea28078ba.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3]
    constant := ![-3, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3]

-- Cycle fingerprint c1deaeb7764b53873903a24434b711e1bfd0343c74ddfe7095cefead4c758d20.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c32b50cdfbc0a7b9b71d2c84e2361113a3986b36498b6e5e9c1f65bb61be8765.
def localCycle00172 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c497a88298a977e4da003dc2dbd7bb3093d487a3782a8426d26562aa87e9e1e9.
def localCycle00173 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .gapLower 0 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint c58887a25deea66258ca13997ec49cf69604a90b09ed51b69b74459280389add.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint c5e0740d2fe9fa119af8488bca17be62ae6a236f73bbcbeb99b1e7785269ce69.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00176 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint c7ad1ddbef40952647f876fba75994c46d6078addd79e9e55542c24bd422fb8e.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 22 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint c7dd1c3a7499306835c102448371c04bcb10c4166c7f28b19635fc8253abec45.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c891c0f88dfadb39f9594bf171725198a3e3aed90ecc2fa347e25990c63c3742.
def localCycle00179 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint c950f9a6b04f953842fa3d7f99efc5a8fe5a342431b9bd34ea048ec1d5d2b86e.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint c9de61f3135ce791ae047be9c4198f4da2bea3e99eb9c17b8803bde9ba2b1125.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint cab47cf4e0c05f7a7dd3c69aa211d4918306ef43f762aecd704f34761c6c6ee4.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint caf399b7b9a06fed31b2c8a88a51616567287dc146ae96fe5ab296de1bec87c2.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint cb20299a8ba674e166854e24d80e2b7a0e9870172fed550098bef5636cddcec7.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 21 2, .gapLower 1 3]

-- Cycle fingerprint cbd00dacfb9c004e1196a2122a899dfde5e8667cbe8a824f68a27cf96a041849.
def localCycle00185 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 2, .triangle 22 1]

-- Cycle fingerprint cc74381878b6dd155eb92fd12884ce22fd8ca26af42b8eb7d94bcb4d1ec39e02.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ccddcee5a6eff03e9e085d513a511ced0e7e0341b663b87895d79c3f11d029f0.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 1 3]
    constant := ![-2, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 1 3]

-- Cycle fingerprint cd77a0c7c461e093bfb730e2fb69785d554b113da323936e56e02ebf556bc73f.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 2 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint cfa454b8e9432c8b4b3baf882ec84703f36cc8311d32003d8a2bb4120236d474.
def localCycle00189 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d4bb3bf206a830cd71f8535a6ef736a20f0a08b33380c3613ff5ba9a08691d44.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d7ec84da5800cfc84971d43c5e07360e008ce90d5b12657cb5f80dda1a514484.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint d9a3c14f35450f92b6881056213d79c996ab0f808f350939ff1e96a75af2df66.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d9d9fee9b823bf16a71f70c16080017de595e75fc65cd9aedd5ab2f5fd4dcd2b.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00194 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dadf41238d665d803fe6f3c78cc11b472212be8835a7429298cea67a0a70a3ac.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dbbf7844d809bb6c0aa1e995533b49ab1aa89391e18436367f01a271f2153e10.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint dbc67c1ede01ced679d2cf56cb7071464e7b596557f0494d88f071d0d997124b.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![0, -1, -1, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 22 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2]

-- Cycle fingerprint dc380938c4cfc996dc9fd9bb27b0a4b790ad291b62c499f27b52eed574df6678.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint deb1562f3f7599e4c49d20250b62ca75ec90a5ae90a3ac039499c2ebd41c3ece.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint dfe78eb973ac5ba52e24ddb56b122a8d09b93a98fe5912c60e67fc1f034f4a73.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint e1dfb219fef0160768247b1dcaeda32e09c10b36ad4dce38b05a762bc42ca752.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 3 2, .triangle 12 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint e343d47f4374fb700efb0043cb0da89362ae755879ac9022186f0178a258fc78.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e449b6228bc7e42b78ca25fcdd2e1f2314982dc709f8c538e2e35874eedf9cf0.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint e5fcd48037c9fb3a296986b840105ea7240a0e0a9f12935c9f2aefe1fbf3967a.
def localCycle00204 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e8eda30dc307caaebeabf0f30f9641a850ef09da407efa692f2264ff9a191af1.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint e93e1a1e113329f1bba856be3960dfefea04e4035079ad76bfca792031ab90e9.
def localCycle00206 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 1 3, .gapLower 1 4, .triangle 24 0]

-- Cycle fingerprint e985c664fdb5bfee35dc7fc7ad7ca7763582e82f220206f8692ad6d9b1e2ec14.
def localCycle00207 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint e9fda8f35ac7d54bd6afdd5eb3757466d0aae9b30d72cde0fe7c30aecf4fc79c.
def localCycle00208 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint ea890687bdf464d428ffd9d2c07e2d3b46a4e51dd6343bd63c8bda9d161a75ef.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4]
    constant := ![-1, 3, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 2 2, .triangle 12 0, .triangle 28 0]

-- Cycle fingerprint eb9dd1fb48497da34b9a287f94b53fb673760a9e74a92f71f64eb7a284c1881a.
def localCycle00210 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint edc634477b67cd3b0fda7d114d3cf8f6c69d12f65d96964e73538122f9431e10.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 22 0, .triangle 12 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 15 2, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint ee7792a0e063614ca1028f3f0a67fb9c4faf48a104445a9d4f10d21adb18400f.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 24 1, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint eee9a4e6edb80fd45dcc3d4e49f3f4fcba543de412a82cf3041825c0fcd39c51.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 23 1, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 19 2, .gapLower 1 3]

-- Cycle fingerprint ef3b52c5e73c788641f406617334523992ffc63afb45056f9ce80c48f7c4f814.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint efe25de85d68d4b033cfa992dc10465ef7cfb68d92f4697f0e403efe4eaf5f99.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint f10d9e3fd5036cdc1e8493b1d410e51696ab5917ac4ccb61a7395fc94427faa6.
def localCycle00216 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true, false, true] }
  origin := ![.triangle 13 1, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint f135a5455f0d75725b2c1bf5eb53ff6d90627692aa8c4ce4b21f0571526bc85e.
def localCycle00217 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f147bf85fa8da137bde117b8b998e3e5de7fab63eab2296135baebd500f909c0.
def localCycle00218 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f5d67582cce9274dfe391e053af3929ecaff24668d1b99b256b61ba14067dd9d.
def localCycle00219 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 14 2, .triangle 11 1, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f633e20c54dd7aceea09a003d49ac7bd95c6a060588e5487da0b775d74b1e545.
def localCycle00220 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![-3, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 5, .gapUpper 3 6, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint f6c344930ef64025f0ee936ce8a1c60a19f67f5aa8c9ef3573ff4c6f40e58ebe.
def localCycle00221 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -3, 0, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint f6e071b50f2475bc8ea0a4cb78a4a03d4565f20296ce86b32b440869f2718480.
def localCycle00222 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f6fc4caa750afd22720ac59e7c64ec2199befb178a6f7a7369966804f1f29aa3.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4]

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

-- Cycle fingerprint f97be7831ed1892db6effbbf84b3fc321cbb7159d7ce38ffc3ecfb172a0d2c30.
def localCycle00226 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .distance 0 6, .theta 6, .theta 5]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, -1, 0]
    strict := ![true, false, false, false, false, false, false, true, true, true] }
  origin := ![.thetaNext 4, .corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 3, .triangle 0 0, .triangle 4 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint f9d0c195b1235283f0f9fe7abbaa4257832f9f7d2cbeb8ad2b45bf210abdbfe0.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fb31de0424395eab7b77d05efe74a5a67a29cea23801f00862ee36f9128e593e.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint fbefff94ea32b0e2e729a53cd051abce54d817f832d64ff878bb992a1c8b1ca4.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, -2, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 22 0, .triangle 12 0, .triangle 2 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint fc017fb4a472e9a5c450706f3012f87d339a3014718d2a14255b5b18ea7d33b4.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint fe28f8e75c997b04c5b43f3d76310700acfc0a1ec8081448efc449b3df01d8f3.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6]
    constant := ![0, -1, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 34 1, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 13 0]

-- Cycle fingerprint fe2fe9058e72b10d853600809e8bc0f722579e280c7cad4a6eaa8e54cbd76644.
def localCycle00232 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint ffea61a06f15b810d616f97cffbaa096a98b0a7d7a607b7f1317ff691d15f793.
def localCycle00233 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 2 0]

def library : Library := fun id => if id < 117 then (if id < 58 then (if id < 29 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 25 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))))) else (if id < 43 then (if id < 36 then (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))))) else (if id < 50 then (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))))))) else (if id < 87 then (if id < 72 then (if id < 65 then (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))))) else (if id < 79 then (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 83 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))))) else (if id < 102 then (if id < 94 then (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 98 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))))) else (if id < 109 then (if id < 105 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))))))) else (if id < 175 then (if id < 146 then (if id < 131 then (if id < 124 then (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))) else (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))))) else (if id < 138 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))) else (if id < 142 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))) else (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)))))) else (if id < 160 then (if id < 153 then (if id < 149 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))))) else (if id < 167 then (if id < 163 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))) else (if id < 165 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)))) else (if id < 171 then (if id < 169 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))))) else (if id < 204 then (if id < 189 then (if id < 182 then (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)))) else (if id < 185 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))))) else (if id < 196 then (if id < 192 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none))) else (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))) else (if id < 200 then (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))) else (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)))))) else (if id < 219 then (if id < 211 then (if id < 207 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))) else (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)))) else (if id < 215 then (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none))) else (if id < 217 then (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))))) else (if id < 226 then (if id < 222 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))) else (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)))) else (if id < 230 then (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none))) else (if id < 232 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6784)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 202 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6785)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 128 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6786)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .tail 128 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6787)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 128 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6788)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 128 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6789)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 172 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6790)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 195 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6791)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![2, 3, 0, 5, 1, 4]], proof := .tail 148 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6792)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 74 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6793)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 164 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6794)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 97 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6795)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 41 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6796)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![2, 3, 0, 5, 4, 1]], proof := .tail 47 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6797)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 34 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6798)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![2, 3, 0, 5, 4, 1]], proof := .tail 219 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6799)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 175 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6800)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6801)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 202 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6802)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 0, 1, 4]], proof := .tail 137 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6803)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 0, 4, 1]], proof := .tail 47 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6804)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 6, 0, 4, 1], ![2, 3, 5, 0, 4, 1]], proof := .tail 26 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6805)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 217 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6806)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 222 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6807)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 68 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6808)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 34 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6809)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 44 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6810)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 82 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6811)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 4, 0, 1]], proof := .tail 140 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6812)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 4, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 142 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6813)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 3 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6814)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 5, 0, 1], ![3, 2, 6, 4, 0, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 144 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6815)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 145 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6816)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 151 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6817)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 2, 0, 1, 4, 5]], proof := .low (![114, 158, 24, 227, 77, 220, 78, 110, 7, 37, 212, 126, 98, 150, 94, 80, 126, 87, 138, 155, 126, 233, 183, 126, 18, 126, 167, 126]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6818)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 2, 0, 1, 5, 4]], proof := .low (![221, 92, 176, 86, 77, 220, 78, 67, 29, 63, 212, 126, 98, 60, 38, 80, 126, 159, 0, 4, 126, 4, 14, 126, 16, 126, 167, 126]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6819)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 1, 4]], proof := .low (![149, 88, 111, 28, 206, 208, 78, 49, 2, 131, 45, 99, 58, 165, 72, 45, 99, 15, 1, 45, 99, 93, 45, 35, 174, 230, 20, 9]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6820)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 1, 4]], proof := .low (![149, 88, 111, 215, 40, 22, 78, 49, 2, 65, 161, 90, 98, 165, 72, 161, 90, 166, 1, 161, 90, 156, 161, 200, 123, 48, 51, 205]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6821)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 196 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6822)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 146 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6823)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 4, 1]], proof := .tail 103 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6824)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 4, 1]], proof := .tail 103 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6825)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 196 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6826)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 62 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6827)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 4, 0, 1]], proof := .tail 103 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6828)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 196 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6829)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 189 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6830)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 168 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6831)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 168 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6832)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 71 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6833)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .low (![173, 225, 185, 105, 143, 160, 78, 36, 214, 54, 229, 55, 211, 59, 54, 154, 55, 8, 54, 12, 197, 59, 95, 89, 184, 122, 85, 180]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6834)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .low (![106, 225, 91, 224, 39, 13, 78, 36, 139, 190, 132, 101, 98, 112, 42, 132, 101, 108, 73, 76, 96, 177, 75, 79, 213, 100, 19, 118]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6835)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 34 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6836)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![3, 2, 0, 5, 4, 1]], proof := .tail 27 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6837)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 6, 0, 4, 1], ![3, 2, 5, 0, 4, 1]], proof := .tail 27 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6838)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 2, 0, 4, 1]], proof := .tail 171 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6839)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 146 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6840)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 4, 1], ![3, 2, 5, 4, 0, 1]], proof := .tail 142 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6841)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 5 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6842)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 142 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6843)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 163 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6844)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 163 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6845)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 117 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6846)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .low (![193, 225, 32, 105, 127, 17, 78, 36, 214, 209, 102, 81, 98, 59, 209, 216, 81, 8, 209, 21, 201, 179, 232, 25, 188, 56, 53, 119]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6847)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 164 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6848)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 175 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6849)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .low (![134, 225, 91, 64, 170, 113, 78, 36, 139, 52, 187, 70, 98, 112, 42, 187, 70, 198, 107, 116, 43, 182, 31, 46, 136, 231, 223, 109]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6850)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 192 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6851)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 153 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6852)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 5, 0, 1], ![3, 2, 6, 4, 0, 1], ![3, 2, 5, 4, 0, 1]], proof := .tail 66 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6853)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 5, 0, 1], ![3, 6, 2, 4, 0, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 204 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6854)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 146 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6855)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 5, 0, 1], ![3, 6, 2, 4, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 169 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6856)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 169 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6857)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 61 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6858)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 186 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6859)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 57 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6860)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6861)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 222 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6862)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 44 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6863)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 145 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6864)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 147 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6865)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 192 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6866)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 153 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6867)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 30 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6868)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 5, 2, 0, 1], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 130 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6869)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 228 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6870)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 69 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6871)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 133 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6872)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 178 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6873)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 121 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6874)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 125 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6875)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 121 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6876)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 152 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6877)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 199 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6878)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 199 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6879)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 199 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6880)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 135 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6881)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 10 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6882)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 10 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6883)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 10 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6884)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 141 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6885)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 181 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6886)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![6, 5, 3, 2, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 129 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6887)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 207 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6888)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 120 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6889)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 83 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6890)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 83 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6891)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 23 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6892)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 83 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6893)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 50 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6894)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 84 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6895)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 124 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6896)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 84 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6897)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6898)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 191 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6899)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 203 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6900)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 1, 2, 5, 3, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 210 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6901)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 1, 2, 5, 3, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 194 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6902)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 1, 2, 5, 3, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 33 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6903)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 4, 3, 5], ![6, 0, 1, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 6 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6904)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 4, 5, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 218 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6905)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 226 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6906)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 104 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6907)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 104 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6908)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 162 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6909)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 157 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6910)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 115 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6911)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6784 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6784 ≤ id.val) (hhigh : id.val < 6912) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6784)) = true := by
  let j : Fin 128 := ⟨id.val - 6784, by omega⟩
  have hsum : 6784 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6784 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard053
