import Mathlib.Order.Interval.Set.Basic
import IptablesSemantics.iptables.decision_state
/-theory L4_Protocol
imports "HOL-Library.Word"
begin

section‹Transport Layer Protocols›
type_synonym primitive_protocol = "8 word"

definition "ICMP ≡ 1 :: 8 word"
definition "TCP ≡ 6 :: 8 word"
definition "UDP ≡ 17 :: 8 word"

context begin
qualified definition "SCTP ≡ 132  :: 8 word"
qualified definition "IGMP ≡ 2 :: 8 word"
qualified definition "GRE ≡ 47 :: 8 word"
qualified definition "ESP ≡ 50 :: 8 word"
qualified definition "AH ≡ 51 :: 8 word"
qualified definition "IPv6ICMP ≡ 58 :: 8 word"
end

datatype protocol = ProtoAny | Proto "primitive_protocol"

fun match_proto :: "protocol ⇒ primitive_protocol ⇒ bool" where
  "match_proto ProtoAny _ ⟷ True" |
  "match_proto (Proto (p)) p_p ⟷ p_p = p"

fun simple_proto_conjunct :: "protocol ⇒ protocol ⇒ protocol option" where
  "simple_proto_conjunct ProtoAny proto = Some proto" |
  "simple_proto_conjunct proto ProtoAny = Some proto" |
  "simple_proto_conjunct (Proto p1) (Proto p2) = (if p1 = p2 then Some (Proto p1) else None)"

lemma simple_proto_conjunct_correct: "match_proto p1 pkt ∧ match_proto p2 pkt ⟷
  (case simple_proto_conjunct p1 p2 of None ⇒ False | Some proto ⇒ match_proto proto pkt)"
  apply(cases p1)
   apply(simp_all)
  apply(cases p2)
   apply(simp_all)
  done

section‹TCP flags›
datatype tcp_flag = TCP_SYN | TCP_ACK | TCP_FIN | TCP_RST | TCP_URG | TCP_PSH

end
-/

/-theory Iface
imports "HOL-Library.Char_ord"
begin

section‹Network Interfaces›

datatype iface = Iface (iface_sel: "string")

definition ifaceAny :: iface where
  "ifaceAny ≡ Iface ''+''"

fun iface_name_is_wildcard :: "string ⇒ bool" where
  "iface_name_is_wildcard [] ⟷ False" |
  "iface_name_is_wildcard [s] ⟷ s = CHR ''+''" |
  "iface_name_is_wildcard (_#ss) ⟷ iface_name_is_wildcard ss"

fun internal_iface_name_match :: "string ⇒ string ⇒ bool" where
  "internal_iface_name_match []     []         ⟷ True" |
  "internal_iface_name_match (i#is) []         ⟷ (i = CHR ''+'' ∧ is = [])" |
  "internal_iface_name_match []     (_#_)      ⟷ False" |
  "internal_iface_name_match (i#is) (p_i#p_is) ⟷ (if (i = CHR ''+'' ∧ is = []) then True else (
        (p_i = i) ∧ internal_iface_name_match is p_is
  ))"

fun match_iface :: "iface ⇒ string ⇒ bool" where
  "match_iface (Iface i) p_iface ⟷ internal_iface_name_match i p_iface"

lemma match_ifaceAny: "match_iface ifaceAny i"
  by(cases i, simp_all add: ifaceAny_def)

fun iface_conjunct :: "iface ⇒ iface ⇒ iface option" where
  "iface_conjunct (Iface i1) (Iface i2) = (case (iface_name_is_wildcard i1, iface_name_is_wildcard i2) of
    (True,  True) ⇒ map_option Iface (internal_iface_name_wildcard_longest i1 i2) |
    (True,  False) ⇒ (if match_iface (Iface i1) i2 then Some (Iface i2) else None) |
    (False, True) ⇒ (if match_iface (Iface i2) i1 then Some (Iface i1) else None) |
    (False, False) ⇒ (if i1 = i2 then Some (Iface i1) else None))"

lemma iface_conjunct_Some: "iface_conjunct i1 i2 = Some x ⟹
      match_iface x p_i ⟷ match_iface i1 p_i ∧ match_iface i2 p_i"

lemma iface_conjunct_None: "iface_conjunct i1 i2 = None ⟹ ¬ (match_iface i1 p_i ∧ match_iface i2 p_i)"

lemma iface_conjunct: "match_iface i1 p_i ∧ match_iface i2 p_i ⟷
       (case iface_conjunct i1 i2 of None ⇒ False | Some x ⇒ match_iface x p_i)"

lemma iface_conjunct_ifaceAny: "iface_conjunct ifaceAny i = Some i"

end
-/
/-theory Simple_Packet
imports L4_Protocol
begin

record 'i simple_packet =
  p_iiface :: string
  p_oiface :: string
  p_src :: "'i::len word"
  p_dst :: "'i word"
  p_proto :: primitive_protocol
  p_sport :: "16 word"
  p_dport :: "16 word"
  p_tcp_flags :: "tcp_flag set"
  p_payload :: string

end
-/

/-theory SimpleFw_Syntax
imports Iface L4_Protocol Simple_Packet Firewall_Common_Decision_State
begin

datatype simple_action = Accept | Drop

record (overloaded) 'i simple_match =
  iiface :: "iface"
  oiface :: "iface"
  src :: "('i::len word × nat)"
  dst :: "('i::len word × nat)"
  proto :: "protocol"
  sports :: "(16 word × 16 word)"
  dports :: "(16 word × 16 word)"

context
  notes [[typedef_overloaded]]
begin
  datatype 'i simple_rule = SimpleRule (match_sel: "'i simple_match") (action_sel: simple_action)
end

definition simple_rule_dtor :: "'a simple_rule ⇒ 'a simple_match × simple_action" where
  "simple_rule_dtor r ≡ (case r of SimpleRule m a ⇒ (m,a))"

end
-/

/-theory SimpleFw_Semantics
imports SimpleFw_Syntax IP_Addresses.IP_Address IP_Addresses.Prefix_Match
begin

fun simple_match_ip :: "('i::len word × nat) ⇒ 'i::len word ⇒ bool" where
  "simple_match_ip (base, len) p_ip ⟷ p_ip ∈ ipset_from_cidr base len"

fun simple_match_port :: "(16 word × 16 word) ⇒ 16 word ⇒ bool" where
  "simple_match_port (s,e) p_p ⟷ p_p ∈ {s..e}"

fun simple_matches :: "'i::len simple_match ⇒ ('i, 'a) simple_packet_scheme ⇒ bool" where
  "simple_matches m p ⟷
    (match_iface (iiface m) (p_iiface p)) ∧
    (match_iface (oiface m) (p_oiface p)) ∧
    (simple_match_ip (src m) (p_src p)) ∧
    (simple_match_ip (dst m) (p_dst p)) ∧
    (match_proto (proto m) (p_proto p)) ∧
    (simple_match_port (sports m) (p_sport p)) ∧
    (simple_match_port (dports m) (p_dport p))"

fun simple_fw :: "'i::len simple_rule list ⇒ ('i, 'a) simple_packet_scheme ⇒ state" where
  "simple_fw [] _ = Undecided" |
  "simple_fw ((SimpleRule m Accept)#rs) p = (if simple_matches m p then Decision FinalAllow else simple_fw rs p)" |
  "simple_fw ((SimpleRule m Drop)#rs) p = (if simple_matches m p then Decision FinalDeny else simple_fw rs p)"

definition simple_match_any :: "'i::len simple_match" where
  "simple_match_any ≡ ⦇iiface=ifaceAny, oiface=ifaceAny, src=(0,0), dst=(0,0), proto=ProtoAny, sports=(0,65535), dports=(0,65535) ⦈"

lemma simple_match_any: "simple_matches simple_match_any p"

definition simple_match_none :: "'i::len simple_match" where
  "simple_match_none ≡ ⦇iiface=ifaceAny, oiface=ifaceAny, src=(1,0), dst=(0,0),
     proto=ProtoAny, sports=(1,0), dports=(0,65535) ⦈"

lemma simple_match_none: "¬ simple_matches simple_match_none p"

fun empty_match :: "'i::len simple_match ⇒ bool" where
  "empty_match ⦇iiface=_, oiface=_, src=_, dst=_, proto=_,
                sports=(sps1, sps2), dports=(dps1, dps2) ⦈ ⟷ (sps1 > sps2) ∨ (dps1 > dps2)"

subsection‹Simple Ports›

fun simpl_ports_conjunct :: "(16 word × 16 word) ⇒ (16 word × 16 word) ⇒ (16 word × 16 word)" where
  "simpl_ports_conjunct (p1s, p1e) (p2s, p2e) = (max p1s p2s, min p1e p2e)"

lemma simple_ports_conjunct_correct:
  "simple_match_port p1 pkt ∧ simple_match_port p2 pkt ⟷ simple_match_port (simpl_ports_conjunct p1 p2) pkt"

subsection‹Simple IPs›

lemma simple_match_ip_conjunct:
  fixes ip1 :: "'i::len word × nat"
  shows "simple_match_ip ip1 p_ip ∧ simple_match_ip ip2 p_ip ⟷
          (case ipcidr_conjunct ip1 ip2 of None ⇒ False | Some ipx ⇒ simple_match_ip ipx p_ip)"

subsection‹Merging Simple Matches›

fun simple_match_and :: "'i::len simple_match ⇒ 'i simple_match ⇒ 'i simple_match option" where
  "simple_match_and ⦇iiface=iif1, oiface=oif1, src=sip1, dst=dip1, proto=p1, sports=sps1, dports=dps1 ⦈
                    ⦇iiface=iif2, oiface=oif2, src=sip2, dst=dip2, proto=p2, sports=sps2, dports=dps2 ⦈ =
    (case ipcidr_conjunct sip1 sip2 of None ⇒ None | Some sip ⇒
    (case ipcidr_conjunct dip1 dip2 of None ⇒ None | Some dip ⇒
    (case iface_conjunct iif1 iif2 of None ⇒ None | Some iif ⇒
    (case iface_conjunct oif1 oif2 of None ⇒ None | Some oif ⇒
    (case simple_proto_conjunct p1 p2 of None ⇒ None | Some p ⇒
    Some ⦇iiface=iif, oiface=oif, src=sip, dst=dip, proto=p,
          sports=simpl_ports_conjunct sps1 sps2, dports=simpl_ports_conjunct dps1 dps2 ⦈)))))"

lemma simple_match_and_correct: "simple_matches m1 p ∧ simple_matches m2 p ⟷
  (case simple_match_and m1 m2 of None ⇒ False | Some m ⇒ simple_matches m p)"

end
-/

/-theory Wordinterval
imports "HOL-Library.Word"
begin

datatype 'a wordinterval =
    WordInterval (wi_start: "'a::len word") (wi_end: "'a word")
  | RangeUnion "'a wordinterval" "'a wordinterval"

fun wordinterval_to_set :: "'a::len wordinterval ⇒ 'a word set" where
  "wordinterval_to_set (WordInterval start end) = {start .. end}" |
  "wordinterval_to_set (RangeUnion r1 r2) = wordinterval_to_set r1 ∪ wordinterval_to_set r2"

definition empty_wordinterval :: "'a::len wordinterval ⇒ bool" where
  "empty_wordinterval r ⟷ wordinterval_to_set r = {}"

fun wordinterval_element :: "'a::len word ⇒ 'a wordinterval ⇒ bool" where
  "wordinterval_element el (WordInterval s e) ⟷ s ≤ el ∧ el ≤ e" |
  "wordinterval_element el (RangeUnion r1 r2) ⟷ wordinterval_element el r1 ∨ wordinterval_element el r2"

lemma wordinterval_element_set_eq: "wordinterval_element el r ⟷ el ∈ wordinterval_to_set r"

definition wordinterval_union :: "'a::len wordinterval ⇒ 'a wordinterval ⇒ 'a wordinterval" where
  "wordinterval_union r1 r2 = RangeUnion r1 r2"

lemma wordinterval_union_set_eq:
  "wordinterval_to_set (wordinterval_union r1 r2) = wordinterval_to_set r1 ∪ wordinterval_to_set r2"

fun wordinterval_intersection :: "'a::len wordinterval ⇒ 'a wordinterval ⇒ 'a wordinterval" where
  "wordinterval_intersection (WordInterval s1 e1) (WordInterval s2 e2) =
     WordInterval (max s1 s2) (min e1 e2)" |
  "wordinterval_intersection (RangeUnion r1 r2) t =
     RangeUnion (wordinterval_intersection r1 t) (wordinterval_intersection r2 t)" |
  "wordinterval_intersection t (RangeUnion r1 r2) =
     RangeUnion (wordinterval_intersection t r1) (wordinterval_intersection t r2)"

lemma wordinterval_intersection_set_eq:
  "wordinterval_to_set (wordinterval_intersection r1 r2) =
   wordinterval_to_set r1 ∩ wordinterval_to_set r2"

definition wordinterval_empty :: "'a::len wordinterval" where
  "wordinterval_empty ≡ WordInterval 1 0"

lemma wordinterval_empty_set_eq: "wordinterval_to_set wordinterval_empty = {}"

definition wordinterval_UNIV :: "'a::len wordinterval" where
  "wordinterval_UNIV ≡ WordInterval 0 (- 1)"

lemma wordinterval_UNIV_set_eq: "wordinterval_to_set wordinterval_UNIV = UNIV"

end
-/

/-theory Prefix_Match
imports Wordinterval
begin

definition ipset_from_cidr :: "'a::len word ⇒ nat ⇒ 'a word set" where
  "ipset_from_cidr pfx len ≡
     let m = mask (LENGTH('a) - len) in
     {pfx AND NOT m .. pfx OR m}"

definition valid_prefix :: "'a::len word × nat ⇒ bool" where
  "valid_prefix ≡ λ(base, len). (base AND mask (LENGTH('a) - len)) = 0"

fun ipcidr_to_interval :: "('a::len word × nat) ⇒ ('a word × 'a word)" where
  "ipcidr_to_interval (base, len) =
     (let m = mask (LENGTH('a) - len) in (base AND NOT m, base OR m))"

definition ipcidr_tuple_to_wordinterval :: "('a::len word × nat) ⇒ 'a wordinterval" where
  "ipcidr_tuple_to_wordinterval ≡ λ(base, len).
     let (s, e) = ipcidr_to_interval (base, len) in WordInterval s e"

fun ipcidr_conjunct :: "('a::len word × nat) ⇒ ('a word × nat) ⇒ ('a word × nat) option" where
  "ipcidr_conjunct (b1, m1) (b2, m2) =
     (if m1 ≥ m2 then
        (if b1 ∈ ipset_from_cidr b2 m2 then Some (b1, m1) else None)
      else
        (if b2 ∈ ipset_from_cidr b1 m1 then Some (b2, m2) else None))"

lemma ipcidr_conjunct_correct:
  "ipset_from_cidr b1 m1 ∩ ipset_from_cidr b2 m2 =
   (case ipcidr_conjunct (b1, m1) (b2, m2) of
      None ⇒ {}
    | Some (b, m) ⇒ ipset_from_cidr b m)"

fun cidr_split :: "'a::len wordinterval ⇒ ('a word × nat) list" where
  "cidr_split (WordInterval s e) =
     (if s > e then []
      else pfxes s e)" |
  "cidr_split (RangeUnion r1 r2) = cidr_split r1 @ cidr_split r2"

lemma cidr_split_prefix:
  "(⋃(ip, n) ∈ set (cidr_split r). ipset_from_cidr ip n) = wordinterval_to_set r"

end
-/

/-
theory Firewall_Common_Decision_State
imports Main
begin

datatype final_decision = FinalAllow | FinalDeny

datatype state = Undecided | Decision final_decision

end

-/

/-record 'i simple_match =
  iiface :: iface
  oiface :: iface
  src    :: "('i word × nat)"
  dst    :: "('i word × nat)"
  proto  :: protocol
  sports :: "(16 word × 16 word)"
  dports :: "(16 word × 16 word)"
-/

abbrev word32 := UInt32
abbrev word16 := UInt16

--
structure simple_match  where
  iiface : Iface
  oiface : Iface
  src    : word32 × Nat
  dst    : word32 × Nat
  proto  : Protocol
  sports : word16 × word16
  dports : word16 × word16

/-fun simple_match_ip :: "('i::len word × nat) ⇒ 'i::len word ⇒ bool" where
  "simple_match_ip (base, len) p_ip ⟷ p_ip ∈ ipset_from_cidr base len"

fun simple_match_port :: "(16 word × 16 word) ⇒ 16 word ⇒ bool" where
  "simple_match_port (s,e) p_p ⟷ p_p ∈ {s..e}"
-/

--check if an ip address is in a CIDR block like 192.168.1.0/24
--(2^8 = 256 addresses from 192.168.1.0 to 192.168.1.225)
-- range is [base, base + 256]
def simple_match_ip (cidr: word32 × Nat) (ip : word32) : Bool :=
  let (base, len) := cidr
  base.toNat <= ip.toNat && ip.toNat < base.toNat + 2^(32-len)

-- does the port p fall within s..e
def simple_match_port : word16 × word16 -> word16 -> Bool
  | (s,e), p => s <= p && p <= e

/-
fun simple_matches :: "'i::len simple_match ⇒ ('i, 'a) simple_packet_scheme ⇒ bool" where
  "simple_matches m p ⟷
    (match_iface (iiface m) (p_iiface p)) ∧
    (match_iface (oiface m) (p_oiface p)) ∧
    (simple_match_ip (src m) (p_src p)) ∧
    (simple_match_ip (dst m) (p_dst p)) ∧
    (match_proto (proto m) (p_proto p)) ∧
    (simple_match_port (sports m) (p_sport p)) ∧
    (simple_match_port (dports m) (p_dport p))"-/

/-fun match_iface :: "iface ⇒ string ⇒ bool" where
  "match_iface (Iface i) p_iface ⟷ internal_iface_name_match i p_iface"
-/
/-
 fun internal_iface_name_match :: "string ⇒ string ⇒ bool" where
      "internal_iface_name_match []     []         ⟷ True" |
      "internal_iface_name_match (i#is) []         ⟷ (i = CHR ''+'' ∧ is = [])" |
      "internal_iface_name_match []     (_#_)      ⟷ False" |
      "internal_iface_name_match (i#is) (p_i#p_is) ⟷ (if (i = CHR ''+'' ∧ is = []) then True else (
            (p_i = i) ∧ internal_iface_name_match is p_is
      ))"
 -/

/- record 'i simple_packet =
  p_iiface :: string
  p_oiface :: string
  p_src :: "'i::len word"
  p_dst :: "'i word"
  p_proto :: primitive_protocol
  p_sport :: "16 word"
  p_dport :: "16 word"
  p_tcp_flags :: "tcp_flag set"
  p_payload :: string

end
-/
-/
def internal_iface_name_match_list : List Char → List Char → Bool
  | [], [] => True
  | i :: is, [] => (i = '+') ∧ is = []
  | [], _ :: _ => False
  | i :: is, p :: ps =>
      if i = '+' ∧ is = [] then True
      else (p = i) ∧ internal_iface_name_match_list is ps

def internal_iface_name_match (i p : String) : Bool :=
  internal_iface_name_match_list i.toList p.toList

structure Iface where
  name : String

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

/-fun match_proto :: "protocol ⇒ primitive_protocol ⇒ bool" where
  "match_proto ProtoAny _ ⟷ True" |
  "match_proto (Proto (p)) p_p ⟷ p_p = p"
-/
abbrev PrimitiveProtocol := UInt8

inductive Protocol where
  | ProtoAny
  | Proto (p : PrimitiveProtocol)

def match_proto : Protocol -> PrimitiveProtocol -> Bool
  | Protocol.ProtoAny, _ => True
  | Protocol.Proto p, p_p => p = p_p

def simple_matches (m : simple_match) (p : simple_packet) : Bool :=
  match_iface m.iiface p.p_iiface &&
  match_iface m.oiface p.p_oiface &&
  simple_match_ip m.src p.p_src &&
  simple_match_ip m.dst p.p_dst &&
  match_proto m.proto p.p_proto &&
  simple_match_port m.sports p.p_sport &&
  simple_match_port m.dports p.p_dport
/-
datatype simple_action = Accept | Drop
-/
inductive simple_action where
  | Accept
  | Drop
/-
datatype 'i simple_rule = SimpleRule (match_sel: "'i simple_match") (action_sel: simple_action)
-/
structure simple_rule where
  match_sel : simple_match
  action_sel: simple_action

open Iptables
def simple_fw : List simple_rule -> simple_packet -> Iptables.ProcessingDecision
  | [], _ => ProcessingDecision.undecided
  | r :: rs, p =>
    if simple_matches r.match_sel p then
      match r.action_sel with
      | simple_action.Accept => ProcessingDecision.decision FinalDecision.allow
      | simple_action.Drop => ProcessingDecision.decision FinalDecision.deny
    else
      simple_fw rs p
