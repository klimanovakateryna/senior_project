import IptablesSemantics.nftables.nf_syntax
import IptablesSemantics.nftables.nf_decision_state
import IptablesSemantics.iptables.semantics
import Aesop
open Nftables


-- Ruleset is a map from chain names to rule lists
abbrev NfRuleset (A : Type) : Type := String -> Option (List (Rule A))

inductive expression_evaluation {A P : Type} (γ : Matcher A P) (p : P) :
Expression A -> Registers -> Registers -> Prop where

  | comparison_true {regs m} :
      matchExpression γ m p = true ->
      expression_evaluation γ p (Expression.Comparison m) regs
        {regs with verdict := Verdict.NFT_CONTINUE}

  | comparison_false {regs m} :
      matchExpression γ m p = false ->
      expression_evaluation γ p (Expression.Comparison m) regs
        {regs with verdict := Verdict.NFT_BREAK}

inductive ExprListEval
  | elist_match     -- all expressions succeeded
  | elist_nomatch -- some expression failed

/-- Evaluate expressions and return whether they elist_match -/
inductive expressions_match {A P : Type} (γ : Matcher A P) (p : P) :
List (Expression A) -> Registers -> ExprListEval -> Prop where
  | empty {regs} :
      expressions_match γ p [] regs ExprListEval.elist_match
  /-- Expression fails: not elist_match -/
  | fail {e es regs regs1} :
      expression_evaluation γ p e regs regs1 ->
      regs1.verdict = Verdict.NFT_BREAK ->
      expressions_match γ p (e :: es) regs ExprListEval.elist_nomatch
  /-- Expression succeeds, continue checking rest -/
  | cont {e es regs regs1 result} :
      expression_evaluation γ p e regs regs1 ->
      regs1.verdict = Verdict.NFT_CONTINUE ->
      expressions_match γ p es regs1 result ->
      expressions_match γ p (e :: es) regs result

/-- Apply a statement to registers -/
def apply_statement (stmt : Statement) (regs : Registers) : Registers :=
  let (v, chain) := statement_to_verdict stmt
  {regs with verdict := v, destination_chain := chain}

open Nftables in
/-- Rule evaluation. If all expressions matched, apply the statement, otherwise skip, and move to the next rule. -/
inductive rule_evaluation {A P : Type} (Γ : NfRuleset A) (γ : Matcher A P) (p : P) :
Rule A -> Registers -> Registers -> Prop where

  /-- The rule expressions' [e1, e2, .., en] all match, so apply statement -/
  | elist_match {r regs st} :
    r.statement = RuleStatement.SingleStatement st ->
    expressions_match γ p r.expressions regs ExprListEval.elist_match ->
    rule_evaluation Γ γ p r regs (apply_statement st regs)

  /-- One rule expression [e1, e2, .., en] does not match. Set verdict to Continue and skip the rule.
  The evaluation proceeds to the next rule. -/
  | elist_nomatch {r regs} :
    expressions_match γ p r.expressions regs ExprListEval.elist_nomatch ->
    rule_evaluation Γ γ p r regs {regs with verdict := Verdict.NFT_CONTINUE}

/-- Ruleset evaluation -/
inductive ruleset_evaluation {A P : Type} (Γ : NfRuleset A) (γ : Matcher A P) (p : P) :
List (Rule A) -> Registers -> Registers -> Prop where

  | skip {regs} :
      ruleset_evaluation Γ γ p [] regs regs

  | accept {r rs regs regs1} :
      regs.verdict = Verdict.NFT_CONTINUE ->
      rule_evaluation Γ γ p r regs regs1 ->
      regs1.verdict = Verdict.NFT_ACCEPT ->
      ruleset_evaluation Γ γ p (r :: rs) regs regs1

  | drop {r rs regs regs1} :
      regs.verdict = Verdict.NFT_CONTINUE ->
      rule_evaluation Γ γ p r regs regs1 ->
      regs1.verdict = Verdict.NFT_DROP ->
      ruleset_evaluation Γ γ p (r :: rs) regs regs1

  | stolen {r rs regs regs1} :
      regs.verdict = Verdict.NFT_CONTINUE ->
      rule_evaluation Γ γ p r regs regs1 ->
      regs1.verdict = Verdict.NFT_STOLEN ->
      ruleset_evaluation Γ γ p (r :: rs) regs regs1

  | nf_continue {r rs regs regs1 regs2} :
      regs.verdict = Verdict.NFT_CONTINUE ->
      rule_evaluation Γ γ p r regs regs1 ->
      regs1.verdict = Verdict.NFT_CONTINUE ->
      ruleset_evaluation Γ γ p rs regs1 regs2 ->
      ruleset_evaluation Γ γ p (r :: rs) regs regs2

  | nf_return {r rs regs regs1} :
      regs.verdict = Verdict.NFT_CONTINUE ->
      rule_evaluation Γ γ p r regs regs1 ->
      regs1.verdict = Verdict.NFT_RETURN ->
      ruleset_evaluation Γ γ p (r :: rs) regs regs1

  | jump {r rs regs regs1 regs2 regs3 chain chain_rules} :
      regs.verdict = Verdict.NFT_CONTINUE ->
      rule_evaluation Γ γ p r regs regs1 ->
      regs1.verdict = Verdict.NFT_JUMP ->
      regs1.destination_chain = some chain ->
      Γ chain = some chain_rules ->
      ruleset_evaluation Γ γ p chain_rules {regs1 with verdict := Verdict.NFT_CONTINUE, destination_chain := none} regs2 ->
      ruleset_evaluation Γ γ p rs
        (if regs2.verdict = Verdict.NFT_RETURN then
          {regs2 with verdict := Verdict.NFT_CONTINUE, destination_chain := none}
        else regs2) regs3 ->
      ruleset_evaluation Γ γ p (r :: rs) regs regs3

  | goto {r rs regs regs1 regs2 chain chain_rules} :
      regs.verdict = Verdict.NFT_CONTINUE ->
      rule_evaluation Γ γ p r regs regs1 ->
      regs1.verdict = Verdict.NFT_GOTO ->
      regs1.destination_chain = some chain ->
      Γ chain = some chain_rules ->
      ruleset_evaluation Γ γ p chain_rules
        {regs1 with verdict := Verdict.NFT_CONTINUE, destination_chain := none} regs2 ->
      ruleset_evaluation Γ γ p (r :: rs) regs regs2

  | terminal {rs regs} :
    (regs.verdict = Verdict.NFT_ACCEPT ∨ regs.verdict = Verdict.NFT_DROP) ->
    ruleset_evaluation Γ γ p rs regs regs

/-- Expression evaluation is deterministic -/
theorem expression_evaluation_determinism {A P : Type} (γ : Matcher A P) (p : P) :
∀ (e : Expression A) (regs regs1 regs2 : Registers),
expression_evaluation γ p e regs regs1 ->
expression_evaluation γ p e regs regs2 ->
regs1 = regs2 := by
  intro e regs regs1 regs2 h1 h2
  cases h1 <;> cases h2 <;> simp_all

/-- Expressions match is deterministic -/
theorem expressions_match_determinism {A P : Type} (γ : Matcher A P) (p : P)
(es : List (Expression A)) (regs : Registers) (r1 r2 : ExprListEval)
(h1 : expressions_match γ p es regs r1) (h2 : expressions_match γ p es regs r2) : r1 = r2 := by
  induction h1 generalizing r2 with
  | empty => cases h2; rfl
  | fail he hv =>
    cases h2 with
    | fail he2 hv2 => rfl
    | cont he2 hv2 _ =>
      have := expression_evaluation_determinism γ p _ _ _ _ he he2
      simp_all
  | cont he hv _ ih =>
    cases h2 with
    | fail he2 hv2 =>
      have := expression_evaluation_determinism γ p _ _ _ _ he he2
      simp_all
    | cont he2 hv2 hrest2 =>
      have heq := expression_evaluation_determinism γ p _ _ _ _ he he2
      subst heq
      exact ih _ hrest2

/-- Rule evaluation is deterministic -/
theorem rule_evaluation_determinism {A P : Type} (Γ : NfRuleset A) (γ : Matcher A P) (p : P) :
    ∀ (r : Rule A) (regs regs1 regs2 : Registers),
    rule_evaluation Γ γ p r regs regs1 ->
    rule_evaluation Γ γ p r regs regs2 ->
    regs1 = regs2 := by
  intro r regs regs1 regs2 h1 h2
  cases h1 with
  | elist_match heq1 hexprs1 =>
    cases h2 with
    | elist_match heq2 hexprs2 => simp_all
    | elist_nomatch hnm2 =>
      have := expressions_match_determinism γ p _ _ _ _ hexprs1 hnm2
      contradiction
  | elist_nomatch hnm1 =>
    cases h2 with
    | elist_match heq2 hexprs2 =>
      have := expressions_match_determinism γ p _ _ _ _ hnm1 hexprs2
      contradiction
    | elist_nomatch hnm2 => rfl

/-- Ruleset evaluation is deterministic -/
theorem ruleset_evaluation_determinism {A P : Type} (Γ : NfRuleset A) (γ : Matcher A P) (p : P)
    (rs : List (Rule A)) (regs regs1 regs2 : Registers)
    (h1 : ruleset_evaluation Γ γ p rs regs regs1)
    (h2 : ruleset_evaluation Γ γ p rs regs regs2) : regs1 = regs2 := by
  induction h1 generalizing regs2 with
  -- empty ruleset: regs unchanged
  | skip =>
    cases h2 with
    | skip => rfl
    | terminal _ => rfl

  -- accept: rule produced NFT_ACCEPT
  | accept verdict_cont rule_eval1 verdict_accept =>
    cases h2 with
    | accept _ rule_eval2 _ =>
      exact rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
    | drop _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | stolen _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_continue _ rule_eval2 _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_return _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | jump _ rule_eval2 _ _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | goto _ rule_eval2 _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | terminal verdict_terminal =>
      simp_all

  -- drop: rule produced NFT_DROP
  | drop verdict_cont rule_eval1 verdict_drop =>
    cases h2 with
    | accept _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | drop _ rule_eval2 _ =>
      exact rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
    | stolen _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_continue _ rule_eval2 _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_return _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | jump _ rule_eval2 _ _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | goto _ rule_eval2 _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | terminal verdict_terminal =>
      simp_all

  | stolen verdict_cont rule_eval1 verdict_stolen =>
    cases h2 with
    | accept _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | drop _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | stolen _ rule_eval2 _ =>
      exact rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
    | nf_continue _ rule_eval2 _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_return _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | jump _ rule_eval2 _ _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | goto _ rule_eval2 _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | terminal verdict_terminal =>
      simp_all

  | nf_return verdict_cont rule_eval1 verdict_return =>
    cases h2 with
    | accept _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | drop _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | stolen _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_continue _ rule_eval2 _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_return _ rule_eval2 _ =>
      exact rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
    | jump _ rule_eval2 _ _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | goto _ rule_eval2 _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | terminal verdict_terminal =>
      simp_all

  | nf_continue verdict_cont rule_eval1 verdict_continue _ ih =>
    cases h2 with
    | accept _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | drop _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | stolen _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_continue _ rule_eval2 _ ruleset_eval2 =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      subst this
      exact ih _ ruleset_eval2
    | nf_return _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | jump _ rule_eval2 _ _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | goto _ rule_eval2 _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | terminal verdict_terminal =>
      simp_all

  | jump verdict_cont rule_eval1 verdict_jump dest_chain1 chain_lookup1 _ _ ih_chain ih_rest =>
    cases h2 with
    | accept _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | drop _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | stolen _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_continue _ rule_eval2 _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_return _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | jump _ rule_eval2 verdict_jump2 dest_chain2 chain_lookup2 chain_eval2 rest_eval2 =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      subst this
      have := dest_chain1.symm.trans dest_chain2
      injection this
      subst_vars
      have := chain_lookup1.symm.trans chain_lookup2
      injection this
      subst_vars
      have := ih_chain _ chain_eval2
      subst this
      exact ih_rest _ rest_eval2
    | goto _ rule_eval2 _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | terminal verdict_terminal =>
      simp_all

  | goto verdict_cont rule_eval1 verdict_goto dest_chain1 chain_lookup1 _ ih_chain =>
    cases h2 with
    | accept _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | drop _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | stolen _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_continue _ rule_eval2 _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | nf_return _ rule_eval2 _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | jump _ rule_eval2 _ _ _ _ _ =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      simp_all
    | goto _ rule_eval2 verdict_goto2 dest_chain2 chain_lookup2 chain_eval2 =>
      have := rule_evaluation_determinism Γ γ p _ _ _ _ rule_eval1 rule_eval2
      subst this
      have := dest_chain1.symm.trans dest_chain2
      injection this
      subst_vars
      have := chain_lookup1.symm.trans chain_lookup2
      injection this
      subst_vars
      exact ih_chain _ chain_eval2
    | terminal verdict_terminal =>
      simp_all

  | terminal verdict_terminal =>
    cases h2 with
    | skip => rfl
    | accept verdict_cont _ _ => simp_all
    | drop verdict_cont _ _ => simp_all
    | stolen verdict_cont _ _ => simp_all
    | nf_continue verdict_cont _ _ _ => simp_all
    | nf_return verdict_cont _ _ => simp_all
    | jump verdict_cont _ _ _ _ _ _ => simp_all
    | goto verdict_cont _ _ _ _ _ => simp_all
    | terminal _ => rfl
