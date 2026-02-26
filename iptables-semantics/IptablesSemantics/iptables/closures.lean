import IptablesSemantics.iptables.ternary_logic
import IptablesSemantics.iptables.syntax
import IptablesSemantics.iptables.semantics
-- 6.2 closures

-- Theorem 5 shows the closure relationship:
-- {in-doubt-deny accepts} ⊆ {exact semantics accepts} ⊆ {in-doubt-allow accepts}

open Iptables KleeneLogic

/-definition in_doubt_allow :: "action ⇒ 'packet ⇒ bool" where
  "in_doubt_allow a p ≡ (a = Accept)"

definition in_doubt_deny :: "action ⇒ 'packet ⇒ bool" where
  "in_doubt_deny a p ≡ (a = Drop ∨ a = Reject)"-/

def in_doubt_allow {P : Type} : unknown_match_tac Action P :=
  fun a _ => a == Action.Accept

def in_doubt_deny {P : Type} : unknown_match_tac Action P :=
  fun a _ => a == Action.Drop || a == Action.Reject

/-
inductive approximating_bigstep ::
  "('a, 'packet) match_tac ⇒ 'packet ⇒ 'a rule list ⇒ state ⇒ state ⇒ bool"
  ("_,_⊢⟨_, _⟩ ⇒α _") where
  skip: "γ,p⊢⟨[], t⟩ ⇒α t" |
  accept: "matches γ m Accept p ⟹ γ,p⊢⟨[Rule m Accept], Undecided⟩ ⇒α Decision FinalAllow" |
  drop: "matches γ m Drop p ⟹ γ,p⊢⟨[Rule m Drop], Undecided⟩ ⇒α Decision FinalDeny" |
  reject: "matches γ m Reject p ⟹ γ,p⊢⟨[Rule m Reject], Undecided⟩ ⇒α Decision FinalDeny" |
  log: "matches γ m Log p ⟹ γ,p⊢⟨[Rule m Log], Undecided⟩ ⇒α Undecided" |
  empty: "matches γ m Empty p ⟹ γ,p⊢⟨[Rule m Empty], Undecided⟩ ⇒α Undecided" |
  nomatch: "¬matches γ m a p ⟹ γ,p⊢⟨[Rule m a], Undecided⟩ ⇒α Undecided" |
  decision: "γ,p⊢⟨rs, Decision X⟩ ⇒α Decision X" |
  seq: "γ,p⊢⟨rs1, Undecided⟩ ⇒α t ⟹ γ,p⊢⟨rs2, t⟩ ⇒α t' ⟹ γ,p⊢⟨rs1@rs2, Undecided⟩ ⇒α t'"
-/
inductive approximating_bigstep {A P : Type}
(γ : match_tac A Action P) (p : P) :
List (Rule A) -> ProcessingDecision -> ProcessingDecision -> Prop where

| skip {t} :
  approximating_bigstep γ p [] t t

| accept {m} :
  ternary_matches γ m Action.Accept p = true ->
  approximating_bigstep γ p [{matchExpr := m, action := Action.Accept}]
    ProcessingDecision.undecided (ProcessingDecision.decision FinalDecision.allow)

| drop {m} :
  ternary_matches γ m Action.Drop p = true ->
  approximating_bigstep γ p [{matchExpr := m, action := Action.Drop}]
    ProcessingDecision.undecided (ProcessingDecision.decision FinalDecision.deny)

| reject {m} :
  ternary_matches γ m Action.Reject p = true ->
  approximating_bigstep γ p [{matchExpr := m, action := Action.Reject}]
    ProcessingDecision.undecided (ProcessingDecision.decision FinalDecision.deny)

| log {m}:
  ternary_matches γ m Action.Log p = true ->
    approximating_bigstep γ p [{matchExpr := m, action := Action.Log}]
      ProcessingDecision.undecided ProcessingDecision.undecided

| empty {m}:
    ternary_matches γ m Action.Empty p = true ->
    approximating_bigstep γ p [{matchExpr := m, action := Action.Empty}]
      ProcessingDecision.undecided ProcessingDecision.undecided

| noMatch {m a}:
  ternary_matches γ m a p = false ->
  approximating_bigstep γ p [{matchExpr := m, action := a}]
  ProcessingDecision.undecided ProcessingDecision.undecided

| decision {rs X}:
    approximating_bigstep γ p rs (ProcessingDecision.decision X) (ProcessingDecision.decision X)

| seq {rs1 rs2 t t'}:
  approximating_bigstep γ p rs1 ProcessingDecision.undecided t ->
  approximating_bigstep γ p rs2 t t' ->
  approximating_bigstep γ p (rs1 ++ rs2) ProcessingDecision.undecided t'

/- The Boolean and ternary matchers agree when ternary returns True or False.
    When ternary returns Unknown, Boolean is the "oracle" that knows truth.
-/
/-
definition matcher_agree_on_exact_matches :: "('a, 'p) matcher ⇒ ('a ⇒ 'p ⇒ ternaryvalue) ⇒ bool" where
  "matcher_agree_on_exact_matches exact approx ≡
     ∀p m. approx m p ≠ TernaryUnknown ⟶ exact m p = the (ternary_to_bool (approx m p))"
-/
/--Both Boolean matcher and ternary matcher agree that whenever ternary matcher β returns
either True or False, and not Unknown, boolean matcher γ returns the same Boolean value.-/
def matcher_agree_on_exact_matches {A P : Type}
(γ : Matcher A P) (β : exact_match_tac A P) : Prop :=
∀ p m, β m p ≠ ternaryvalue.TernaryUnknown ->
γ m p = (ternary_to_bool (β m p)).get!

/- The closure theorems require good_ruleset rs to ensure no chain jumps exists.
Used as a precondition in closure theorems.-/
/-definition good_ruleset :: "'a rule list ⇒ bool" where
  "good_ruleset rs ≡ ∀r ∈ set rs. get_action r ≠ Call ∧ get_action r ≠ Return ∧
                                   get_action r ≠ Goto ∧ get_action r ≠ Unknown"
-/
def good_ruleset {A : Type} (rs : List (Rule A)) : Prop :=
∀ r ∈ rs, (∀ c, r.action ≠ Action.Call c) ∧
          r.action ≠ Action.Return ∧
          (∀ c, r.action ≠ Action.Goto c) ∧
          r.action ≠ Action.Unknown

/-definition βmagic :: "('a, 'p) matcher ⇒ ('a ⇒ 'p ⇒ ternaryvalue)" where
  "βmagic γ ≡ (λa p. if γ a p then TernaryTrue else TernaryFalse)"
-/
/-- Converts a Boolean matcher into a ternary matcher that never returns.
-/
def βmagic {A P : Type } (γ : Matcher A P) : exact_match_tac A P :=
  fun a p => if γ a p then ternaryvalue.TernaryTrue else ternaryvalue.TernaryFalse
