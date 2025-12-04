import IptablesSemantics.nf_syntax

open Nftables

abbrev Ruleset (A : Type) : Type := String -> Option (List (Rule A))

/--Given a primitive of type A and packet of type B, return whether the primitive matches the packet -/
abbrev Matcher (A P : Type) : Type := A -> P -> Bool


/--For matcher γ and packet p, the evaluation of the expression e in register state r produces new register state r1.
    -/
inductive expression_evaluation {A P : Type } (γ : Matcher A P) (p : P) : Expression A -> Registers -> Registers -> Prop where

/-- Sets the verdict register to a specified value -/
| set {regs v chain}:
    expression_evaluation γ p (Expression.setVerdict v chain) regs { regs with verdict := v,  destination_chain := chain }

/-- In kernel nft_cmp_eval. -/
| compare_true {regs primitive} :
    γ primitive p = true -> expression_evaluation γ p (Expression.Compare primitive) regs regs

| compare_false {regs primitive} :
    γ primitive p = false -> expression_evaluation γ p (Expression.Compare primitive) regs { regs with verdict := Verdict.NFT_BREAK }

/--Evaluation on the rule level. -/
inductive rule_evaluation {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P) : List (Expression A) -> Registers -> Registers -> Prop where

/--
  Code that corresponds to the rule:
  for (; !rule->is_last ; rule = nft_rule_next(rule)) {
    nft_rule_dp_for_each_expr(expr, last, rule) {
    ..
    if (regs.verdict.code != NFT_CONTINUE)
            break;
    }

    case NFT_BREAK:
			regs.verdict.code = NFT_CONTINUE;
			nft_trace_copy_nftrace(pkt, &info);
			continue;

    -/
| noMatch {e es regs regs1} :
    expression_evaluation γ p e regs regs1 ->
    regs1.verdict = Verdict.NFT_BREAK ->
    rule_evaluation Γ γ p (e :: es) regs { regs1 with verdict := Verdict.NFT_CONTINUE }

/-- nft_rule_dp_for_each_expr(expr, last, rule) {
    ..
    if (regs.verdict.code != NFT_CONTINUE)
        break;

    switch (regs.verdict.code & NF_VERDICT_MASK) {
        case NF_ACCEPT:
        ..
        return regs.verdict.code;
    -/
| accept {e es regs regs1} :
  expression_evaluation γ p e regs regs1 ->
  regs1.verdict = Verdict.NFT_ACCEPT ->
  rule_evaluation Γ γ p (e :: es) regs regs1

| drop {e es regs regs1} :
  expression_evaluation γ p e regs regs1 ->
  regs1.verdict = Verdict.NFT_DROP ->
  rule_evaluation Γ γ p (e :: es) regs regs1

| empty {regs} : rule_evaluation Γ γ p [] regs regs

| nf_continue {e es regs regs1 regs2} :
    expression_evaluation γ p e regs regs1 ->
    regs1.verdict = Verdict.NFT_CONTINUE ->
    rule_evaluation Γ γ p es regs1 regs2 ->
    rule_evaluation Γ γ p (e :: es) regs regs2


/-- Evaluation on the chain level. -/
inductive ruleset_evaluation {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P) : List (Rule A) -> Registers -> Registers -> Prop where

| seq {rs1 rs2 regs regs1 regs2} :
  ruleset_evaluation Γ γ p rs1 regs regs1 ->
  regs1.verdict = Verdict.NFT_CONTINUE ->
  ruleset_evaluation Γ γ p rs2 regs1 regs2 ->
  ruleset_evaluation Γ γ p (rs1 ++ rs2) regs regs2

| decision {rs regs} :
  is_decided regs.verdict = true ->
  ruleset_evaluation Γ γ p rs regs regs

/--case NFT_JUMP:
    jumpstack[stackptr].rule = nft_rule_next(rule);  // Save NEXT rule after current
    stackptr++;
    fallthrough;
  case NFT_GOTO:
    chain = regs.verdict.chain;
    goto do_chain;  (jump to target chain)

  if (stackptr > 0) {
    stackptr--;
    rule = jumpstack[stackptr].rule;  -- restore prev position
    goto next_rule;
}-/
| jump {r rs regs regs1 regs2 regs3 chain_rules chain} :
    rule_evaluation Γ γ p r.expressions regs regs1 ->
    regs1.verdict = Verdict.NFT_JUMP ->
    regs1.destination_chain = some chain ->
    Γ chain = some chain_rules ->
    ruleset_evaluation Γ γ p chain_rules regs1 regs2 ->
    ruleset_evaluation Γ γ p rs regs2 regs3 ->
    ruleset_evaluation Γ γ p (r :: rs) regs regs3

| goto {r rs regs regs1 regs2 chain_rules chain} :
  rule_evaluation Γ γ p r.expressions regs regs1 ->
   regs1.verdict = Verdict.NFT_GOTO ->
   regs1.destination_chain = some chain ->
   Γ chain = some chain_rules ->
   ruleset_evaluation Γ γ p chain_rules regs1 regs2 ->
   ruleset_evaluation Γ γ p (r :: rs) regs regs2

| nf_return {r rs regs regs1} :
  rule_evaluation Γ γ p r.expressions regs regs1 ->
  regs1.verdict = Verdict.NFT_RETURN ->
  ruleset_evaluation Γ γ p (r :: rs) regs regs1

| skip {regs} :
  ruleset_evaluation Γ γ p [] regs regs

| accept {r rs regs regs1} :
    rule_evaluation Γ γ p r.expressions regs regs1 ->
    regs1.verdict = Verdict.NFT_ACCEPT ->
    ruleset_evaluation Γ γ p (r :: rs) regs regs1

| drop {r rs regs regs1} :
    rule_evaluation Γ γ p r.expressions regs regs1 ->
    regs1.verdict = Verdict.NFT_DROP ->
    ruleset_evaluation Γ γ p (r :: rs) regs regs1

| nf_continue {r rs regs regs1 regs2} :
    rule_evaluation Γ γ p r.expressions regs regs1 ->
    regs1.verdict = Verdict.NFT_CONTINUE ->
    ruleset_evaluation Γ γ p rs regs1 regs2 ->
    ruleset_evaluation Γ γ p (r :: rs) regs regs2


/-- Determinism for the expression level. For any expression e and register states regs, regs1, regs2,
    if evaluating e from regs gives regs1, and evaluating e from regs gives regs2, then regs1 = regs2 -/
theorem expression_evaluation_determinism {A P : Type} (γ : Matcher A P) (p : P) :
∀ (e : Expression A) (regs regs1 regs2 : Registers),
expression_evaluation γ p e regs regs1 ->
expression_evaluation γ p e regs regs2 ->
regs1 = regs2 := by
intro e regs regs1 regs2 h1 h2 --introduces hypotheses
/-split on h1 and h2 (set/compare_true/compare_false, with 9 cases),
and then simplify them -/
cases h1
all_goals cases h2
all_goals simp_all





/--For any expression list es and register states regs, regs1, regs2,
  if evaluating es from regs gives regs1, nd evaluating es from regs gives regs2, then regs1 = regs2.-/
theorem rule_evaluation_determinism {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P) :
∀ (es : List (Expression A)) (regs regs1 regs2 : Registers),
rule_evaluation Γ γ p es regs regs1 ->
rule_evaluation Γ γ p es regs regs2 →
regs1 = regs2 := by
intro e regs regs1 regs2 h1 h2

/- empty {regs} : rule_evaluation Γ γ p [] regs regs-/

/-Proof by structural induction on hypothesis 1.
h1 - rule_evaluation Γ γ p es regs regs1
h2 - rule_evaluation Γ γ p es regs regs2
-/
induction h1 generalizing regs2 with

/-Base case.
  Both use empty constructor: regs1 = regs and regs2 = regs.
-/
| empty =>
  -- creates subcase: empty.empty
  cases h2
  . rfl

/-
| noMatch {e es regs regs1} :
    expression_evaluation γ p e regs regs1 ->
    regs1.verdict = Verdict.NFT_BREAK ->
    rule_evaluation Γ γ p (e :: es) regs { regs1 with verdict := Verdict.NFT_CONTINUE }-/

/- Case 1: h1 uses noMatch constructor.

-/
| noMatch h1_exp_evaluation h1_verdict =>
    cases h2 with
    | noMatch h2_exp_evaluation h2_verdict =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ h1_exp_evaluation h2_exp_evaluation
      simp_all

    | accept h2_exp_evaluation verdict_accept2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ h1_exp_evaluation h2_exp_evaluation
      simp_all

    | drop h2_exp_evaluation verdict_drop2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ h1_exp_evaluation h2_exp_evaluation
      simp_all

    | nf_continue h2_exp_evaluation verdict_continue2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ h1_exp_evaluation h2_exp_evaluation
      simp_all

| accept exp_evaluation1 verdict_accept1  =>
    cases h2 with
    | noMatch exp_evaluation2 verdict_break2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | accept exp_evaluation2 verdict_accept2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

     | drop exp_evaluation2 verdict_drop2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | nf_continue exp_evaluation2 verdict_continue2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

| drop exp_evaluation1 verdict_drop1 =>
    cases h2 with
    | noMatch exp_evaluation2 verdict_break2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | accept exp_evaluation2 verdict_accept2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | drop exp_evaluation2 verdict_drop2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | nf_continue exp_evaluation2 verdict_continue2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

/-| nf_continue {r rs regs regs1 regs2} :
    rule_evaluation Γ γ p r.expressions regs regs1 ->
    regs1.verdict = Verdict.NFT_CONTINUE ->
    ruleset_evaluation Γ γ p rs regs1 regs2 ->
    ruleset_evaluation Γ γ p (r :: rs) regs regs2
-/
| nf_continue exp_evaluation1 verdict_continue1 rule_eval ih2 =>
    cases h2 with
    | noMatch exp_evaluation2 verdict_break2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | accept exp_evaluation2 verdict_accept2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | drop exp_evaluation2 verdict_drop2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      simp_all

    | nf_continue exp_evaluation2 verdict_continue2 rule_eval2 =>
      have single_expr_determinism := expression_evaluation_determinism γ p _ _ _ _ exp_evaluation1 exp_evaluation2
      subst single_expr_determinism
      apply ih2
      assumption



theorem  ruleset_evaluation_deterministic {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P) :
∀ (rs : List (Rule A)) (regs regs1 regs2 : Registers),
ruleset_evaluation Γ γ p rs regs regs1 ->
ruleset_evaluation Γ γ p rs regs regs2 ->
regs1 = regs2 := by
intro rs regs regs1 regs2 h1 h2
induction h1 generalizing regs2 with


/- for iptables, they did
 lemma seq_progress:
     "Γ,γ,p⊢ ⟨rs, s⟩ ⇒ t ⟹ rs = rs⇩1@rs⇩2 ⟹
      Γ,γ,p⊢ ⟨rs⇩1, s⟩ ⇒ t' ⟹ Γ,γ,p⊢ ⟨rs⇩2, t'⟩ ⇒ t"
-/

/-| seq {rs1 rs2 regs regs1 regs2} :
  ruleset_evaluation Γ γ p rs1 regs regs1 →
  regs1.verdict = Verdict.NFT_CONTINUE →
  ruleset_evaluation Γ γ p rs2 regs1 regs2 →
  ruleset_evaluation Γ γ p (rs1 ++ rs2) regs regs2-/
| seq h1_rs_list h1_rs_verdict h1_rule_eval ih =>
  sorry

| decision h1_decided =>
  sorry

| skip =>
  sorry

/-| jump {r rs regs regs1 regs2 regs3 chain_rules chain} :
    rule_evaluation Γ γ p r.expressions regs regs1 ->
    regs1.verdict = Verdict.NFT_JUMP ->
    regs1.destination_chain = some chain ->
    Γ chain = some chain_rules ->
    ruleset_evaluation Γ γ p chain_rules regs1 regs2 ->
    ruleset_evaluation Γ γ p rs regs2 regs3 ->
    ruleset_evaluation Γ γ p (r :: rs) regs regs3-/
| jump h1_rule_eval h1_rule_verdict h1_target_chain h1_env h1_jump_eval h1_rest_eval ih_target ih_rest =>
  sorry

/- goto {r rs regs regs1 regs2 chain_rules chain} :
  rule_evaluation Γ γ p r.expressions regs regs1 ->
   regs1.verdict = Verdict.NFT_GOTO ->
   regs1.destination_chain = some chain ->
   Γ chain = some chain_rules ->
   ruleset_evaluation Γ γ p chain_rules regs1 regs2 ->
   ruleset_evaluation Γ γ p (r :: rs) regs regs2 -/
| goto h1_rule_eval h1_verdict h1_chain_name h1_chain h1_goto_eval =>
sorry

| nf_return h1_rule_eval h1_verdict =>
sorry

| drop h1_rule_eval h1_verdict =>
sorry

| nf_continue h1_rule_eval h1_verdict_continue2 h1_rule_eval =>
sorry

| accept h1_rule_eval h1_verdict =>
sorry







































--/--Evaluation on the rule level. -/
--inductive rule_evaluation {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P) : List (Expression A) -> Registers -> Registers -> Prop where
