import Mathlib.Order.Interval.Set.Basic
import IptablesSemantics.iptables.decision_state
import IptablesSemantics.nftables.nf_syntax

structure Iface where
  name : String

abbrev PrimitiveProtocol := UInt8

inductive Protocol where
  | ProtoAny
  | Proto (p : PrimitiveProtocol)

abbrev word32 := UInt32
abbrev word16 := UInt16

-- datatype represents a set of IPs built from closed intervals and unions
inductive word32_inv where
  | Interval (lower upper : word32) --closed interval
  | Union (a : word32_inv) (b : word32_inv) -- unions of many cidrs/ranges in one set
  | UniversalSet
  | EmptySet

inductive word16_inv where
  | Interval (lower upper : word16) --closed interval
  | Union (a b : word16_inv) -- unions of many cidrs/ranges in one set
  | UniversalSet
  | EmptySet

-- simple_match_ip is replaced by this
def word32_member (ip : word32) : word32_inv -> Bool
  | .Interval s e => s ≤ ip && ip ≤ e
  | .Union a b => word32_member ip a || word32_member ip b
  | .UniversalSet => true
  | .EmptySet => false

def word16_member (ip : word16) : word16_inv -> Bool
  | .Interval s e => s ≤ ip && ip ≤ e
  | .Union a b => word16_member ip a || word16_member ip b
  | .UniversalSet => true
  | .EmptySet => false

structure nf_simple_match  where
  iiface : Iface
  oiface : Iface
  src    : word32_inv -- union of intervals
  dst    : word32_inv
  proto  : Protocol
  sports : word16_inv -- union of port ranges
  dports : word16_inv

-- def simple_match_ip (cidr: word32 × Nat) (ip : word32) : Bool :=
--   let (base, len) := cidr
--   base.toNat <= ip.toNat && ip.toNat < base.toNat + 2^(32-len)

-- def simple_match_port : word16 × word16 -> word16 -> Bool
--   | (s,e), p => s <= p && p <= e

def internal_iface_name_match_list : List Char → List Char → Bool
  | [], [] => True
  | i :: is, [] => (i = '+') ∧ is = []
  | [], _ :: _ => False
  | i :: is, p :: ps =>
      if i = '+' ∧ is = [] then True
      else (p = i) ∧ internal_iface_name_match_list is ps

def internal_iface_name_match (i p : String) : Bool :=
  internal_iface_name_match_list i.toList p.toList

def match_iface (i : Iface) (p_iface : String) : Bool :=
  internal_iface_name_match i.name p_iface

structure simple_packet where
  p_iiface : String
  p_oiface : String
  p_src : word32
  p_dst : word32
  p_proto : PrimitiveProtocol
  p_sport : word16
  p_dport : word16

def match_proto : Protocol -> PrimitiveProtocol -> Bool
  | Protocol.ProtoAny, _ => True
  | Protocol.Proto p, p_p => p = p_p

def nf_simple_matches (m : nf_simple_match) (p : simple_packet) : Bool :=
  match_iface m.iiface p.p_iiface &&
  match_iface m.oiface p.p_oiface &&
  word32_member p.p_src m.src &&
  word32_member p.p_dst m.dst &&
  match_proto m.proto p.p_proto &&
  word16_member p.p_sport m.sports &&
  word16_member p.p_dport m.dports

inductive simple_action where
  | Accept
  | Drop

structure nf_simple_rule where
  match_sel : nf_simple_match
  action_sel: simple_action

open Nftables

def nf_simple_fw : List nf_simple_rule -> simple_packet -> Verdict
  | [], _ => Verdict.NFT_CONTINUE
  | r :: rs, p =>
    if nf_simple_matches r.match_sel p then
      match r.action_sel with
      | simple_action.Accept => Verdict.NFT_ACCEPT
      | simple_action.Drop => Verdict.NFT_DROP
    else
      nf_simple_fw rs p

def ifaceAny : Iface := ⟨"+"⟩

def ICMP : PrimitiveProtocol := 1
def TCP : PrimitiveProtocol := 6
def UDP : PrimitiveProtocol := 17

def nf_simple_match_any : nf_simple_match := {
  iiface := ifaceAny,
  oiface := ifaceAny,
  src := .UniversalSet,
  dst := .UniversalSet,
  proto := Protocol.ProtoAny,
  sports := .UniversalSet,
  dports := .UniversalSet
}

def simple_match_none : nf_simple_match := {
  iiface := ifaceAny,
  oiface := ifaceAny,
  src := .EmptySet,
  dst := .UniversalSet,
  proto := .ProtoAny,
  sports := .EmptySet,
  dports := .UniversalSet
}

--find an overlap between the two ranges
def intersection_itv32 (s1 e1 s2 e2 : word32) : word32_inv :=
  let first_itv := max s1 s2
  let second_itv := min e1 e2
  if first_itv ≤ second_itv then
    word32_inv.Interval first_itv second_itv
  else
    word32_inv.EmptySet

def intersection_itv16 (s1 e1 s2 e2 : word16) : word16_inv :=
  let first_itv := max s1 s2
  let second_itv := min e1 e2
  if first_itv ≤ second_itv then
    word16_inv.Interval first_itv second_itv
  else
    word16_inv.EmptySet

def intersection_itv32_sets : word32_inv -> word32_inv -> word32_inv
  -- all ips
  -- All ∩ B
  | .UniversalSet, b => b
  | a, .UniversalSet => a
  | .Interval s1 e1, .Interval s2 e2 => intersection_itv32 s1 e1 s2 e2
  | .Union a b, c => .Union (intersection_itv32_sets a c) (intersection_itv32_sets b c)
  | a, .Union b c => .Union (intersection_itv32_sets a b) (intersection_itv32_sets a c)
  | .EmptySet, _ => .EmptySet
  | _, .EmptySet => .EmptySet

def intersection_itv16_sets : word16_inv -> word16_inv -> word16_inv
  -- all ips
  -- All ∩ B
  | .UniversalSet, b => b
  | a, .UniversalSet => a
  | .Interval s1 e1, .Interval s2 e2 => intersection_itv16 s1 e1 s2 e2
  | .Union a b, c => .Union (intersection_itv16_sets a c) (intersection_itv16_sets b c)
  | a, .Union b c => .Union (intersection_itv16_sets a b) (intersection_itv16_sets a c)
  | .EmptySet, _ => .EmptySet
  | _, .EmptySet => .EmptySet


-- def simpl_ports_conjunct : (word16 × word16) → (word16 × word16) → (word16 × word16)
--   | (p1s, p1e), (p2s, p2e) => (max p1s p2s, min p1e p2e)

def simple_proto_conjunct : Protocol → Protocol → Option Protocol
  | .ProtoAny, proto => some proto
  | proto, .ProtoAny => some proto
  | .Proto p1, Protocol.Proto p2 => if p1 == p2 then some (Protocol.Proto p1) else none

def iface_conjunct (i1 i2 : Iface) : Option Iface :=
  if i1.name == i2.name then some i1
  else if match_iface i1 i2.name then some i2
  else if match_iface i2 i1.name then some i1
  else none

def word32_inv_empty : word32_inv -> Bool
  | .EmptySet => true
  | .UniversalSet => false
  | .Interval s e => s > e
  | .Union a b => word32_inv_empty a && word32_inv_empty b

def word16_inv_empty : word16_inv -> Bool
  | .EmptySet => true
  | .UniversalSet => false
  | .Interval s e => s > e
  | .Union a b => word16_inv_empty a && word16_inv_empty b

def nf_empty_match (m : nf_simple_match) : Bool :=
  word16_inv_empty m.sports || word16_inv_empty m.dports ||
  word32_inv_empty m.src || word32_inv_empty m.dst

-- def ipcidr_conjunct (c1 c2 : word32 × Nat) : Option (word32 × Nat) :=
--   let (b1, m1) := c1
--   let (b2, m2) := c2
--   if m1 >= m2 then
--     if simple_match_ip c2 b1 then some c1 else none
--   else
--     if simple_match_ip c1 b2 then some c2 else none

def nf_simple_match_and (m1 m2 : nf_simple_match) : Option nf_simple_match :=
      match iface_conjunct m1.iiface m2.iiface with
      | none => none
      | some iif =>
        match iface_conjunct m1.oiface m2.oiface with
        | none => none
        | some oif =>
        match simple_proto_conjunct m1.proto m2.proto with
        | none => none
        | some p =>
          some {
            iiface := iif,
            oiface := oif,
            src := intersection_itv32_sets m1.src m2.src,
            dst := intersection_itv32_sets m1.dst m2.dst,
            proto := p,
            sports := intersection_itv16_sets m1.sports m2.sports,
            dports := intersection_itv16_sets m1.dports m2.dports
          }

-- def empty_match (m : simple_match) : Bool :=
--   (m.sports.fst > m.sports.snd) || (m.dports.fst > m.dports.snd)
