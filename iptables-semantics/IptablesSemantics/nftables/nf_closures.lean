import IptablesSemantics.iptables.ternary_logic
import IptablesSemantics.nftables.nf_syntax
import IptablesSemantics.nftables.nf_semantics

open Nftables KleeneLogic

def nf_in_doubt_allow {P : Type} : unknown_match_tac Statement P :=
  fun s _ => s  == Statement.Accept

def nf_in_doubt_deny {P : Type} : unknown_match_tac Statement P :=
  fun s _ => s  == Statement.Drop

def nf_βmagic {A P : Type} (γ : Matcher A P)
: exact_match_tac A P :=
  fun a p => if γ a p then ternaryvalue.TernaryTrue else ternaryvalue.TernaryFalse

def nf_good_ruleset {A : Type} (rs : List (Nftables.Rule A)) : Prop :=
  ∀ r ∈ rs, match r.statement with
  | RuleStatement.SingleStatement s =>
      (∀  c, s ≠ Statement.Jump c) ∧
      (∀  c, s ≠ Statement.Goto c) ∧
      s ≠ Statement.Return
  | RuleStatement.MapLookup _ _ => False

-- nftables with ternary logic
inductive nf_ternary_expression_evaluation {A P : Type}
(γ : match_tac A Statement P) (p : P) (s : Statement) :
Expression A -> Registers -> Registers -> Prop
| comparison_true {regs m}:
  ternary_matches γ m s p = true ->
  nf_ternary_expression_evaluation γ p s (Expression.Comparison m) regs
  {regs with verdict := Verdict.NFT_CONTINUE}
| comparison_false {regs m}:
  ternary_matches γ m s p = false ->
  nf_ternary_expression_evaluation γ p s (Expression.Comparison m) regs
  {regs with verdict := Verdict.NFT_BREAK}

inductive nf_ternary_expressions_match {A P : Type}
(γ : match_tac A Statement P) (p : P) (s : Statement) :
List (Expression A) -> Registers -> ExprListEval -> Prop
| empty {regs} :
    nf_ternary_expressions_match γ p s [] regs ExprListEval.elist_match
| fail {e es regs regs1} :
    nf_ternary_expression_evaluation γ p s e regs regs1 ->
    regs1.verdict = Verdict.NFT_BREAK ->
    nf_ternary_expressions_match γ p s (e :: es) regs ExprListEval.elist_nomatch
| cont {e es regs regs1 res} :
    nf_ternary_expression_evaluation γ p s e regs regs1 ->
    regs1.verdict = Verdict.NFT_CONTINUE ->
    nf_ternary_expressions_match γ p s es regs1 res ->
    nf_ternary_expressions_match γ p s (e :: es) regs res

inductive nf_ternary_rule_evaluation {A P : Type}
(Γ : NfRuleset A) (γ : match_tac A Statement P) (p : P) :
Rule A -> Registers -> Registers -> Prop
| elist_match {r regs st} :
  r.statement = RuleStatement.SingleStatement st ->
  nf_ternary_expressions_match γ p st r.expressions regs ExprListEval.elist_match ->
  nf_ternary_rule_evaluation Γ γ p r regs (apply_statement st regs)
| elist_nomatch {r regs st} :
    r.statement = RuleStatement.SingleStatement st ->
    nf_ternary_expressions_match γ p st r.expressions regs ExprListEval.elist_nomatch ->
    nf_ternary_rule_evaluation Γ γ p r regs {regs with verdict := Verdict.NFT_CONTINUE}

inductive nf_ternary_ruleset_evaluation {A P : Type}
(Γ : NfRuleset A)(γ : match_tac A Statement P) (p : P) :
List (Rule A) -> Registers -> Registers -> Prop where
| skip :
  nf_ternary_ruleset_evaluation Γ γ p [] regs regs
| accept  :
    regs.verdict = Verdict.NFT_CONTINUE ->
    nf_ternary_rule_evaluation Γ γ p r regs regs1 ->
    regs1.verdict = Verdict.NFT_ACCEPT ->
    nf_ternary_ruleset_evaluation Γ γ p (r :: rs) regs regs1
| drop :
    regs.verdict = Verdict.NFT_CONTINUE ->
    nf_ternary_rule_evaluation Γ γ p r regs regs1 ->
    regs1.verdict = Verdict.NFT_DROP ->
    nf_ternary_ruleset_evaluation Γ γ p (r :: rs) regs regs1

| stolen :
    regs.verdict = Verdict.NFT_CONTINUE ->
    nf_ternary_rule_evaluation Γ γ p r regs regs1 ->
    regs1.verdict = Verdict.NFT_STOLEN ->
    nf_ternary_ruleset_evaluation Γ γ p (r :: rs) regs regs1

| nf_continue :
  regs.verdict = Verdict.NFT_CONTINUE ->
  nf_ternary_rule_evaluation Γ γ p r regs regs1 ->
  regs1.verdict = Verdict.NFT_CONTINUE ->
  nf_ternary_ruleset_evaluation Γ γ p rs regs1 regs2 ->
  nf_ternary_ruleset_evaluation Γ γ p (r :: rs) regs regs2

| nf_return :
  regs.verdict = Verdict.NFT_CONTINUE ->
  nf_ternary_rule_evaluation Γ γ p r regs regs1 ->
  regs1.verdict = Verdict.NFT_RETURN ->
  nf_ternary_ruleset_evaluation Γ γ p (r :: rs) regs regs1

| jump :
  regs.verdict = Verdict.NFT_CONTINUE ->
  nf_ternary_rule_evaluation Γ γ p r regs regs1 ->
  regs1.verdict = Verdict.NFT_JUMP ->
  regs1.destination_chain = some chain ->
  Γ chain = some chain_rules ->
  nf_ternary_ruleset_evaluation Γ γ p chain_rules {regs1 with verdict := Verdict.NFT_CONTINUE, destination_chain := none} regs2 ->
  nf_ternary_ruleset_evaluation Γ γ p rs
  (if regs2.verdict = Verdict.NFT_RETURN then
  {regs2 with verdict := Verdict.NFT_CONTINUE, destination_chain := none}
  else regs2) regs3 ->
  nf_ternary_ruleset_evaluation Γ γ p (r :: rs) regs regs3

| goto :
  regs.verdict = Verdict.NFT_CONTINUE ->
  nf_ternary_rule_evaluation Γ γ p r regs regs1 ->
  regs1.verdict = Verdict.NFT_GOTO ->
  regs1.destination_chain = some chain ->
  Γ chain = some chain_rules ->
  nf_ternary_ruleset_evaluation Γ γ p chain_rules
  {regs1 with verdict := Verdict.NFT_CONTINUE, destination_chain := none} regs2 ->
  nf_ternary_ruleset_evaluation Γ γ p (r :: rs) regs regs2

| terminal :
  (regs.verdict = Verdict.NFT_ACCEPT ∨ regs.verdict = Verdict.NFT_DROP) ->
  nf_ternary_ruleset_evaluation Γ γ p rs regs regs
