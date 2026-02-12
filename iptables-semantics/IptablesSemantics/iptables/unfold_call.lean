import IptablesSemantics.iptables.semantics

open Iptables

namespace ChainUnfolding


/- add-match m = map (λr. Rule (MatchAnd m (get-match r)) (get-action r))
-/
def add_match {A : Type} (m : MatchExpr A) (rs : List (Rule A)) : List (Rule A) :=
  -- apply function to each element of rs r
  -- new match m and original
  rs.map fun r => { matchExpr := MatchExpr.MatchAnd m r.matchExpr, action := r.action}

/-Process return
fun process-ret :: ′a rule list ⇒ ′a rule list where
  process-ret [] = [] |
  process-ret (Rule m Return # rs) = add-match (MatchNot m) (process-ret rs) |
  process-ret (r # rs) = r # process-ret rs
-/

/-- Removes Return actions from a ruleset by encoding into match conditions
-/
def process_ret {A : Type} : List (Rule A) -> List (Rule A)
  | [] => []
  | ⟨m, Action.Return⟩ :: rs => add_match (MatchExpr.MatchNot m) (process_ret rs)
  | r :: rs => r :: process_ret rs

/-fun process-call :: ′a ruleset ⇒ ′a rule list ⇒ ′a rule list where
  process-call Γ [] = [] |
  process-call Γ (Rule m (Call chain) # rs) =
      add-match m (process-ret (the (Γ chain))) @ process-call Γ rs |
  process-call Γ (r # rs) = r # process-call Γ rs
 -/
 def process_call {A : Type} (Γ : Ruleset A) : List (Rule A) -> List (Rule A)
 | [] => []
 | ⟨m, Action.Call chain⟩ :: rs => add_match m (process_ret ((Γ chain).getD [])) ++ process_call Γ rs
 | r :: rs => r :: process_call Γ rs

/-un repeat_stabilize :: "nat ⇒ ('a ⇒ 'a) ⇒ 'a ⇒ 'a" where
  "repeat_stabilize 0 f a = a" |
  "repeat_stabilize (Suc n) f a = repeat_stabilize n f (f a)"
-/
/-- Applies function f to value a exactly n times.
    Allows multi-level calls (in Isabelle they allow up to 1000)
    Nat.succ n is n + 1-/
def repeat_stabilize {A : Type} (n : Nat) (f : A -> A) (a : A) : A :=
  match n with
  | 0 => a
  | Nat.succ n => repeat_stabilize n f (f a)

/- Isabelle
definition rm_LogEmpty :: "'a rule list ⇒ 'a rule list" where
  "rm_LogEmpty rs ≡ filter (λr. get_action r ≠ Log ∧ get_action r ≠ Empty) rs"-/

/--Removes all rules with Log or Empty actions from the ruleset.-/
def rm_LogEmpty {A : Type} (rs : List (Rule A)) : List (Rule A) :=
  rs.filter fun r => r.action != Action.Log && r.action != Action.Empty

/-
definition rw_Reject :: "'a rule list ⇒ 'a rule list" where
  "rw_Reject rs ≡ map (λr. case get_action r of
      Reject ⇒ Rule (get_match r) Drop
    | _ ⇒ r) rs"
-/
/--Replaces all Reject with Drop actions-/
def rw_Reject {A : Type} (rs : List (Rule A)) : List (Rule A) :=
  rs.map fun r => match r.action with
  | Action.Reject => ⟨r.matchExpr, Action.Drop⟩
  | _ => r

/-optimize_matches f rs ≡ map (λr. Rule (f (get_match r)) (get_action r)) rs
-/
def optimize_matches {A : Type} (f : MatchExpr A -> MatchExpr A) (rs : List (Rule A)) : List (Rule A) :=
  rs.map fun r => {matchExpr := f r.matchExpr, action := r.action}

/- -- Isabelle
fun opt_MatchAny_match_expr :: "'a match_expr ⇒ 'a match_expr" where
  "opt_MatchAny_match_expr MatchAny = MatchAny" |
  "opt_MatchAny_match_expr (Match a) = Match a" |
  "opt_MatchAny_match_expr (MatchNot MatchAny) = MatchNot MatchAny" |
  "opt_MatchAny_match_expr (MatchNot m) = MatchNot (opt_MatchAny_match_expr m)" |
  "opt_MatchAny_match_expr (MatchAnd MatchAny m) = opt_MatchAny_match_expr m" |
  "opt_MatchAny_match_expr (MatchAnd m MatchAny) = opt_MatchAny_match_expr m" |
  "opt_MatchAny_match_expr (MatchAnd m1 m2) = MatchAnd (opt_MatchAny_match_expr m1) (opt_MatchAny_match_expr m2)"
-/

/--Simplify MatchAny-/
def opt_MatchAny_match_expr {A : Type} : MatchExpr A -> MatchExpr A
  | MatchExpr.MatchAny => MatchExpr.MatchAny
  | MatchExpr.Match a => MatchExpr.Match a
  | MatchExpr.MatchNot MatchExpr.MatchAny => MatchExpr.MatchNot MatchExpr.MatchAny
  | MatchExpr.MatchNot m => MatchExpr.MatchNot (opt_MatchAny_match_expr m)
  | MatchExpr.MatchAnd MatchExpr.MatchAny m => opt_MatchAny_match_expr m
  | MatchExpr.MatchAnd m MatchExpr.MatchAny => opt_MatchAny_match_expr m
  | MatchExpr.MatchAnd m1 m2 => MatchExpr.MatchAnd (opt_MatchAny_match_expr m1) (opt_MatchAny_match_expr m2)

/-simple_ruleset rs ≡ ∀r ∈ set rs. get_action r = Accept ∨ get_action r = Drop
-/
def simple_ruleset {A : Type} (rs : List (Rule A)) : Bool :=
  rs.all fun r => r.action == Action.Accept || r.action == Action.Drop

/-
definition unfold_optimize_ruleset_CHAIN
  :: "('a match_expr ⇒ 'a match_expr) ⇒ string ⇒ action ⇒ 'a ruleset ⇒ 'a rule list option"
where
  "unfold_optimize_ruleset_CHAIN optimize chain_name default_action rs =
    (let rs = (repeat_stabilize 1000 (optimize_matches opt_MatchAny_match_expr)
               (optimize_matches optimize
                 (rw_Reject (rm_LogEmpty (repeat_stabilize 10000 (process_call rs)
                   [Rule MatchAny (Call chain_name), Rule MatchAny default_action])))))
     in if simple_ruleset rs then Some rs else None)"-/

def unfold_optimize_ruleset_CHAIN {A : Type}
    (optimize : MatchExpr A -> MatchExpr A)
    (chain_name : String)
    (default_action : Action)
    (Γ : Ruleset A) : Option (List (Rule A)) :=
  let rs :=
    repeat_stabilize 1000 (optimize_matches opt_MatchAny_match_expr)
      (optimize_matches optimize
      (rw_Reject (rm_LogEmpty (repeat_stabilize 10000 (process_call Γ)
      [⟨MatchExpr.MatchAny, Action.Call chain_name⟩, ⟨MatchExpr.MatchAny, default_action⟩]))))
  if simple_ruleset rs then some rs else none

end ChainUnfolding
