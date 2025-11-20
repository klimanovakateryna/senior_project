import IptablesSemantics.syntax
import IptablesSemantics.decision_state

open Firewall
/-- A firewall ruleset is a map of chain names to the list of rules.
    Partial map from string to list of rules. -/
abbrev Ruleset (A : Type) : Type := String -> Option (List (Firewall.Rule A)) -- Ruleset A is an shorthand for a func that maps a chain name to a list

/--A matcher (parametrized by the type of primitive A and packet P)
is a function which just tells whether a given primitive and packet matches-/
abbrev Matcher (A P : Type) : Type := A -> P -> Bool

/--Turns matchExpr AST into boolean-/
def matchExpression {A P : Type} (γ : Matcher A P) :
  MatchExpr A -> P -> Bool
| MatchExpr.Match a, p => γ a p -- if exp is raw a, use a primitive matcher γ on a and p
| MatchExpr.MatchNot m, p => !(matchExpression γ m p)
| MatchExpr.MatchAnd m₁ m₂, p => matchExpression γ m₁ p && matchExpression γ m₂ p
| MatchExpr.MatchAny, _ => true

inductive iptables_bigstep {A P : Type}
  (Γ : Ruleset A) (γ : Matcher A P) (p : P) : List (Rule A) -> ProcessingDecision -> ProcessingDecision -> Prop where
  | skip {t} : iptables_bigstep Γ γ p [] t t
  | accept {m} : matchExpression γ m p = true -> iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Accept }] ProcessingDecision.undecided (ProcessingDecision.decision FinalDecision.allow)
  | drop {m} : matchExpression γ m p = true -> iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Drop }] ProcessingDecision.undecided (ProcessingDecision.decision FinalDecision.deny)
  | reject {m} : matchExpression γ m p = true -> iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Reject }] ProcessingDecision.undecided (ProcessingDecision.decision FinalDecision.deny)
  | log {m} : matchExpression γ m p = true -> iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Log }] ProcessingDecision.undecided ProcessingDecision.undecided
  | empty {m} : matchExpression γ m p = true -> iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Empty }] ProcessingDecision.undecided ProcessingDecision.undecided
  | noMatch {m a} : matchExpression γ m p = false -> iptables_bigstep Γ γ p [{ matchExpr := m, action := a }] ProcessingDecision.undecided ProcessingDecision.undecided
  | decision {rs X} :iptables_bigstep Γ γ p rs (ProcessingDecision.decision X) (ProcessingDecision.decision X)
  | seq {rs1 rs2 t t'} : iptables_bigstep Γ γ p rs1 ProcessingDecision.undecided t -> iptables_bigstep Γ γ p rs2 t t' -> iptables_bigstep Γ γ p (rs1 ++ rs2) ProcessingDecision.undecided t'
  | call_return {m chain rs₁ m' rs₂} : matchExpression γ m p = true -> Γ chain = some (rs₁ ++ [{ matchExpr := m', action := Action.Return }] ++ rs₂) ->
    matchExpression γ m' p = true -> iptables_bigstep Γ γ p rs₁ ProcessingDecision.undecided ProcessingDecision.undecided ->
    iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Call chain }] ProcessingDecision.undecided ProcessingDecision.undecided
  | call_result {m chain rs t} : matchExpression γ m p = true -> Γ chain = some rs ->
    iptables_bigstep Γ γ p rs ProcessingDecision.undecided t ->
    iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Call chain }] ProcessingDecision.undecided t
