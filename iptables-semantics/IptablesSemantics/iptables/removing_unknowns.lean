import IptablesSemantics.iptables.closures

open Iptables KleeneLogic
-- 7.2 Removing Unknown Primitives

/-definition unknown_match_all :: "'a unknown_match_tac ⇒ action ⇒ bool" where
  "unknown_match_all α a = (∀p. α a p)"
-/
-- Computable version: generic over decision type DES, takes a specific packet p
def unknown_match_all {DES P : Type} (α : unknown_match_tac DES P) (d : DES) (p : P) : Bool :=
  α d p

/-definition unknown_not_match_any :: "'a unknown_match_tac ⇒ action ⇒ bool" where
  "unknown_not_match_any α a = (∀p. ¬α a p)"-/
-- Computable version: generic over decision type DES, takes a specific packet p
def unknown_not_match_any {DES P : Type} (α : unknown_match_tac DES P) (d : DES) (p : P) : Bool :=
  !α d p

/--- Check if expression has unknowns
fun has_unknowns :: "('a, 'p) exact_match_tac ⇒ 'a match_expr ⇒ bool" where
  "has_unknowns β (Match A) = (∃p. ternary_ternary_eval (map_match_tac β p (Match A)) = TernaryUnknown)" |
  "has_unknowns β (MatchNot m) = has_unknowns β m" |
  "has_unknowns β MatchAny = False" |
  "has_unknowns β (MatchAnd m1 m2) = (has_unknowns β m1 ∨ has_unknowns β m2)"-/
def has_unknowns {A P : Type} (β : exact_match_tac A P) : MatchExpr A -> Prop
  | MatchExpr.Match a => ∃ p, β a p = ternaryvalue.TernaryUnknown
  | MatchExpr.MatchNot m => has_unknowns β m
  | MatchExpr.MatchAny => False
  | MatchExpr.MatchAnd m1 m2 => has_unknowns β m1 ∨ has_unknowns β m2

/- Packet independence properties
definition packet_independent_α :: "'p unknown_match_tac ⇒ bool" where
  "packet_independent_α α = (∀a p1 p2. a = Accept ∨ a = Drop ⟶ α a p1 ⟷ α a p2)"-/
def packet_independent_α {P : Type} (α : unknown_match_tac Action P) : Prop :=
  ∀ a p1 p2, (a = Action.Accept ∨ a = Action.Drop) -> (α a p1 = α a p2)

/-definition packet_independent_β_unknown :: "('a, 'packet) exact_match_tac ⇒ bool" where
  "packet_independent_β_unknown β ≡ ∀A. (∃p. β A p ≠ TernaryUnknown) ⟶ (∀p. β A p ≠ TernaryUnknown)"
-/
def packet_independent_β_unknown {A P : Type} (β : exact_match_tac A P) : Prop :=
    ∀ a, (∃ p, β a p ≠ ternaryvalue.TernaryUnknown) ->
         (∀ p, β a p ≠ ternaryvalue.TernaryUnknown)


def isMatchAny {A : Type} : MatchExpr A -> Bool
  | MatchExpr.MatchAny => true
  | _ => false

def isMatchNotAny {A : Type} : MatchExpr A -> Bool
  | MatchExpr.MatchNot MatchExpr.MatchAny => true
  | _ => false

-- Generic over decision type DES (works for both iptables Action and nftables Statement)
def remove_unknowns_generic {A DES P : Type}
  (γ : match_tac A DES P) (d : DES) (p : P) : MatchExpr A -> MatchExpr A
  -- MatchAny stays MatchAny
  | MatchExpr.MatchAny => MatchExpr.MatchAny

  -- ¬MatchAny stays ¬MatchAny (never matches)
  | MatchExpr.MatchNot MatchExpr.MatchAny => MatchExpr.MatchNot MatchExpr.MatchAny

  -- primitive match
  | MatchExpr.Match m =>
      let (β, α) := γ
      if β m p == ternaryvalue.TernaryUnknown then
        if unknown_match_all α d p then MatchExpr.MatchAny
        else if unknown_not_match_any α d p then MatchExpr.MatchNot MatchExpr.MatchAny
        else MatchExpr.Match m
      else MatchExpr.Match m

  -- negated primitive match
  | MatchExpr.MatchNot (MatchExpr.Match m) =>
      let (β, α) := γ
      if β m p == ternaryvalue.TernaryUnknown then
        if unknown_match_all α d p then MatchExpr.MatchNot MatchExpr.MatchAny
        else if unknown_not_match_any α d p then MatchExpr.MatchAny
        else MatchExpr.MatchNot (MatchExpr.Match m)
      else MatchExpr.MatchNot (MatchExpr.Match m)

  -- double negation ¬¬m = m
  | MatchExpr.MatchNot (MatchExpr.MatchNot m) =>
      remove_unknowns_generic γ d p m

  -- conjunction
  | MatchExpr.MatchAnd m1 m2 =>
      MatchExpr.MatchAnd (remove_unknowns_generic γ d p m1) (remove_unknowns_generic γ d p m2)

  -- De Morgan: ¬(m1 ∧ m2) = ¬m1 ∨ ¬m2
  | MatchExpr.MatchNot (MatchExpr.MatchAnd m1 m2) =>
      let r1 := remove_unknowns_generic γ d p (MatchExpr.MatchNot m1)
      let r2 := remove_unknowns_generic γ d p (MatchExpr.MatchNot m2)
      if isMatchAny r1 || isMatchAny r2 then MatchExpr.MatchAny
      else if isMatchNotAny r1 then r2
      else if isMatchNotAny r2 then r1
      else MatchExpr.MatchNot (MatchExpr.MatchAnd (MatchExpr.MatchNot r1) (MatchExpr.MatchNot r2))
