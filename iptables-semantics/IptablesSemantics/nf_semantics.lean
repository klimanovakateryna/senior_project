import IptablesSemantics.nf_syntax


open Nftables


abbrev Ruleset (A : Type) : Type := String -> Option (List (Rule A))

/--Given a primitive of type A and packet of type B, return whether the primitive matches the packet -/
abbrev Matcher (A P : Type) : Type := A -> P -> Bool

/--For matcher γ and packet p, the evaluation of the expression e in register state r produces new register state r1-/
inductive expression_evaluation {A P : Type } (γ : Matcher A P) (p : P) : Expression A -> Registers -> Registers -> Prop where

/-- Sets the verdict register to a specified value -/
| set {regs v chain}:
    expression_evaluation γ p (Expression.setVerdict v chain) regs { regs with verdict := v,  destination_chain := chain }

/-- In kernel nft_cmp_eval. -/
| compare_true {regs primitive} :
    γ primitive p = true -> expression_evaluation γ p (Expression.Compare primitive) regs regs

| compare_false {regs primitive} :
    γ primitive p = false -> expression_evaluation γ p (Expression.Compare primitive) regs { regs with verdict := Verdict.NFT_BREAK }


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

-- theorem nftables_ruleset_deterministic:
--   ruleset_evaluation Γ γ p rs regs regs1 ->
--   ruleset_evaluation Γ γ p rs regs regs2 ->
--   regs1 = regs2 := by
