import IptablesSemantics.iptables.unfold_call
import IptablesSemantics.nftables.nf_syntax
import IptablesSemantics.nftables.nf_semantics
namespace NftablesChainUnfolding

 /-Rule inlining algorithms for nftables -/

#print ChainUnfolding.add_match

/--Prepends a new Comparison expression to each rule's expression list and used during chain unfolding to
   calling rule's match condition into the called chain -/
def nf_add_match {A : Type} (m : MatchExpr A) (rs : List (Nftables.Rule A)) : List (Nftables.Rule A) :=
  rs.map fun r =>
    { expressions := Nftables.Expression.Comparison m :: r.expressions,
      sideEffects := r.sideEffects,
      statement := r.statement }

/-
   [e1,e2,e3] -> (e1 AND e2 AND e3)
-/
def exprs_to_match {A : Type} : List (Nftables.Expression A) -> MatchExpr A
  | [] => MatchExpr.MatchAny -- no m's = always matches
  | [Nftables.Expression.Comparison m] => m -- single exprs = unwrap
  | (Nftables.Expression.Comparison m) :: es => MatchExpr.MatchAnd m (exprs_to_match es)  -- multiple exprs = AND together


/--extends to different rules-/
def nf_unfold_maps_rule {A : Type}
(es : List (Nftables.Expression A))
(se : List Nftables.SideEffect)
(map : Nftables.NfMap A) :
List (Nftables.Rule A) :=
  map.map fun (m, st) => ⟨es ++ [Nftables.Expression.Comparison (MatchExpr.Match m)], se, Nftables.RuleStatement.SingleStatement st⟩

/--lookup + extend-/
def nf_expand {A : Type} (lookup : Nftables.NfLookup) : List (Nftables.Rule A) -> List (Nftables.Rule A)
  | [] => []
  | ⟨es, se, Nftables.RuleStatement.MapLookup mapName m⟩ :: rs =>
    nf_unfold_maps_rule es se ((lookup mapName).getD []) ++ nf_expand lookup rs

#print ChainUnfolding.process_ret

/---/
def nf_process_ret {A : Type} : List (Nftables.Rule A) -> List (Nftables.Rule A)
  | [] => []
  | ⟨exprs, _, Nftables.RuleStatement.SingleStatement Nftables.Statement.Return⟩ :: rs =>
    let m := exprs_to_match exprs
    nf_add_match (MatchExpr.MatchNot m) (nf_process_ret rs)
  | r :: rs => r :: nf_process_ret rs

open Nftables in
def nf_process_call {A : Type} (Γ : NfRuleset A) : List (Nftables.Rule A) -> List (Nftables.Rule A)
  | [] => [] --return empty list
  | ⟨exprs, _, Nftables.RuleStatement.SingleStatement Nftables.Statement.Jump chain⟩ :: rs => -- first rule is ⟨exprs, _, Jump chain⟩
    let target_chain := (Γ chain).getD [] -- chain lookup
    let m := exprs_to_match exprs -- [e1,e2,e3] transforms to (e1 ∧ e2 ∧ e3)
    nf_add_match m (nf_process_ret target_chain) ++ nf_process_call Γ rs -- eliminate returns, and prepend match to an inlined rule
  | r :: rs => r :: nf_process_call Γ rs

 def nf_process_goto {A : Type} (Γ : NfRuleset A) : List (Nftables.Rule A) -> List (Nftables.Rule A)
  | [] => []
  | ⟨exprs, _, Nftables.RuleStatement.SingleStatement Nftables.Statement.Goto chain⟩ :: rs =>
    let target_chain := (Γ chain).getD []
    let m := exprs_to_match exprs
    nf_add_match m (nf_process_ret target_chain)
    ++
    nf_add_match (MatchExpr.MatchNot m) (nf_process_goto Γ rs)
  | r :: rs => r :: nf_process_goto Γ rs

def nf_simple_ruleset {A : Type} (rs : List (Nftables.Rule A)) : Bool :=
  rs.all fun r => r.statement == Nftables.Statement.Accept || r.statement == Nftables.Statement.Drop

-- optimization function f applied to all match exprs
def nf_optimize_matches {A : Type}
  (f : MatchExpr A -> MatchExpr A)
  (rs : List (Nftables.Rule A)) :
  List (Nftables.Rule A) :=
  rs.map fun ⟨es, se, st⟩ =>
    let optimized_match := es.map fun e => match e with
      | Nftables.Expression.Comparison m => Nftables.Expression.Comparison (f m)
    ⟨ optimized_match, se, st⟩

def nf_unfold_chain {A : Type}
    (chain_name : String)
    (default_statement : Nftables.Statement)
    (Γ : NfRuleset A)
    (lookup : Nftables.NfLookup A): Option (List (Nftables.Rule A)) :=
  let rs :=
    ChainUnfolding.repeat_stabilize 1000
      (nf_optimize_matches ChainUnfolding.opt_MatchAny_match_expr)
      (ChainUnfolding.repeat_stabilize 10000
        (fun rs => nf_process_goto Γ (nf_process_call Γ (nf_expand lookup rs)))
        [⟨[], [], Nftables.RuleStatement.SingleStatement Nftables.Statement.Jump chain_name⟩, ⟨[], [], Nftables.RuleStatement.SingleStatement default_statement⟩])
  if nf_simple_ruleset rs then some rs else none

end NftablesChainUnfolding
