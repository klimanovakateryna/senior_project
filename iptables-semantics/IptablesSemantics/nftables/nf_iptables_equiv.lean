import IptablesSemantics.nftables.nf_syntax
import IptablesSemantics.nftables.nf_semantics
import IptablesSemantics.iptables.semantics
import Mathlib.Tactic
import Hammer
open Iptables
open Nftables

inductive simulation : ProcessingDecision -> Registers -> Prop where
  | undecided :
    simulation ProcessingDecision.undecided
    { verdict := Verdict.NFT_CONTINUE, destination_chain := none}
  | allow :
    simulation (ProcessingDecision.decision FinalDecision.allow)
    { verdict := Verdict.NFT_ACCEPT, destination_chain := none}
  | deny :
    simulation (ProcessingDecision.decision FinalDecision.deny)
    { verdict := Verdict.NFT_DROP, destination_chain := none }

/-- The iptables initial state (undecided) and nftables initial state (initial_register)
   satisfy the simulation relation -/
theorem simul_initial : simulation ProcessingDecision.undecided initial_register := by
  unfold initial_register
  exact simulation.undecided

/-- Determinism for simulation relation  each ProcessingDecision maps exactly one Registers state
-/
theorem simRel_deterministic : ∀ (pd : ProcessingDecision) (r1 r2 : Registers),
                              simulation pd r1 -> simulation pd r2 -> r1 = r2 := by
  intro pd r1 r2 h1 h2
  cases h1 <;>
  cases h2 <;>
  rfl

/--Totality for simulation relation = rach iptables state has a corresponding nftables state.
   -/
theorem simrel_total : ∀ (pd : ProcessingDecision), ∃ (r : Registers),
simulation pd r := by
  intro pd
  cases pd with
  | undecided =>
    use { verdict := Verdict.NFT_CONTINUE, destination_chain := none }
    apply simulation.undecided
  | decision d =>
    cases d with
    | allow =>
      use { verdict := Verdict.NFT_ACCEPT, destination_chain := none }
      apply simulation.allow
    | deny =>
      use { verdict := Verdict.NFT_DROP, destination_chain := none }
      apply simulation.deny

/-- ProcessingDecision to Registers.
   -/
def state_to_regs : ProcessingDecision -> Registers
  | ProcessingDecision.undecided =>
    {verdict := Verdict.NFT_CONTINUE, destination_chain := none}
  | ProcessingDecision.decision Iptables.FinalDecision.allow =>
    {verdict := Verdict.NFT_ACCEPT, destination_chain := none}
  | ProcessingDecision.decision Iptables.FinalDecision.deny =>
    {verdict := Verdict.NFT_DROP, destination_chain := none}

/-- state_to_regs is consistent with simulation -/
theorem state_to_regs_simrel : ∀ (pd : ProcessingDecision), simulation pd (state_to_regs pd) := by
  intro pd
  cases pd with
  | undecided => exact simulation.undecided
  | decision d =>
    cases d with
    | allow => exact simulation.allow
    | deny => exact simulation.deny

/-- state_to_regs undecided equals initial_register-/
theorem state_to_regs_undecided :
  state_to_regs ProcessingDecision.undecided = initial_register :=
  rfl

def translate_match {A : Type} : MatchExpr A -> Expression A
  | m => Expression.Comparison m

/-- translate iptables Action to nftables Statement-/
def action_to_statement : Action -> Statement
  | Action.Accept => Statement.Accept
  | Action.Drop => Statement.Drop
  | Action.Reject => Statement.Drop
  | Action.Call chain => Statement.Jump chain
  | Action.Goto chain => Statement.Goto chain
  | Action.Return => Statement.Return
  | Action.Log => Statement.Continue
  | Action.Empty => Statement.Continue
  | Action.Unknown => Statement.Continue

/--Rule translation: convert iptables rule to nftables rule
   The match expression becomes a single comparison expression,
   and the action becomes a statement -/
def rule_translation {A : Type} : Iptables.Rule A -> Nftables.Rule A
  | {matchExpr := m, action := a} =>
    { expressions := [translate_match m],
      statement := action_to_statement a }

/--Ruleset translation-/
def ruleset_translation {A : Type} : List (Iptables.Rule A) -> List (Nftables.Rule A)
  | [] => []
  | r :: rs => rule_translation r :: ruleset_translation rs

/--Translate a ruleset map from iptables to nftables-/
def translate_ruleset {A : Type} (Γ : Ruleset A) : NfRuleset A :=
  fun chain => Option.map ruleset_translation (Γ chain)


/-- If the iptables match expression m succeeds on packet p,
then the translated nftables expression list [ translation (m) ] also succeds.-/
lemma l1_match {A P : Type} (γ : Matcher A P) (p : P) (m : MatchExpr A) (regs : Registers)
  (hmatch : matchExpression γ m p = true) :
  expressions_match γ p [translate_match m] regs ExprListEval.elist_match := by

  unfold translate_match
  apply expressions_match.cont
  -- ⊢ expression_evaluation γ p (have m := m; Expression.Comparison m false) regs ?regs1
  -- comparison_true applies with matchExp = true
  case a => exact expression_evaluation.comparison_true hmatch
  -- ⊢ { verdict := Verdict.NFT_CONTINUE, destination_chain := regs.destination_chain }.verdict = Verdict.NFT_CONTINUE
  -- after comparison_true, Verdict.NFT_CONTINUE by def
  case a => rfl
  --⊢ expressions_match γ p [] { verdict := Verdict.NFT_CONTINUE, destination_chain := regs.destination_chain } ExprListEval.elist_match
  case a => exact expressions_match.empty

/--If the iptables match expression m doesn’t succeed on packet p,
then the translated nftables expression list [ translation (m) ] also doesn’t succeed. -/
lemma l1_nomatch {A P : Type}
    (γ : Matcher A P) (p : P) (m : MatchExpr A) (regs : Registers)
    (hmatch : matchExpression γ m p = false) :
    expressions_match γ p [translate_match m] regs ExprListEval.elist_nomatch := by

  unfold translate_match
  apply expressions_match.fail
  -- ⊢ expression_evaluation γ p (have m := m; Expression.Comparison m false) regs ?regs1
  case a => exact expression_evaluation.comparison_false hmatch
  -- hmatch : matchExpression γ m p = false
  -- ⊢ matchExpression γ m p = false
  case a => rfl

/-- Base case for forward simulation.
Accept in iptables => Accept in nftables (if an iptables ule with Accept
matches a packet, then the translated nftables rule
gives an equivalent NFT_ACCEPT verdict.)
-/
theorem accept_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P)(m : MatchExpr A)  (p : P)

(hyp_match : matchExpression γ m p = true) :

∃ regs, ruleset_evaluation (translate_ruleset Γ) γ p
(ruleset_translation [{ matchExpr := m, action := Action.Accept }]) initial_register regs
∧ simulation (ProcessingDecision.decision FinalDecision.allow) regs := by

  use { initial_register with verdict := Verdict.NFT_ACCEPT, destination_chain := none }
  apply And.intro
  case h.left =>
    apply ruleset_evaluation.accept
    · rfl
    · apply rule_evaluation.elist_match
      exact l1_match γ p m initial_register hyp_match
    · rfl
  case h.right =>
    exact simulation.allow


theorem drop_rej_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(m : MatchExpr A) (hyp_match : matchExpression γ m p = true) :
∃ regs, ruleset_evaluation (translate_ruleset Γ) γ p
(ruleset_translation [{ matchExpr := m, action := Action.Drop }])
initial_register regs
∧ simulation (ProcessingDecision.decision FinalDecision.deny) regs := by
  use { initial_register with verdict := Verdict.NFT_DROP, destination_chain := none }
  apply And.intro
  case h.left =>
    apply ruleset_evaluation.drop
    · rfl
    · apply rule_evaluation.elist_match
      exact l1_match γ p m initial_register hyp_match
    · rfl
  case h.right =>
    exact simulation.deny


/--If the iptables rule does not match the packet, then the translated nftables
rule also does not match, so the rule is skipped and the verdict says NFT_CONTINUE-/
theorem noMatch_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(m : MatchExpr A) (a : Action) (hyp_match : matchExpression γ m p = false) :
∃ regs, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := a }]) initial_register regs
∧ simulation ProcessingDecision.undecided regs := by
  -- ⊢ ∃ regs, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := a }]) initial_register regs ∧
  -- simulation ProcessingDecision.undecided regs
  -- the witness is Continue for noMatch
  use { initial_register with verdict := Verdict.NFT_CONTINUE, destination_chain := none }
  apply And.intro
  -- h.left :⊢ ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := a }]) initial_register
  --(let __src := initial_register;
  --{ verdict := Verdict.NFT_CONTINUE, destination_chain := __src.destination_chain })
  -- h.right: ⊢ simulation ProcessingDecision.undecided
  --(let __src := initial_register;
  -- { verdict := Verdict.NFT_CONTINUE, destination_chain := __src.destination_chain })
  case h.left =>
    apply ruleset_evaluation.nf_continue
    -- ⊢ initial_register.verdict = Verdict.NFT_CONTINUE
    · rfl
    -- ⊢ rule_evaluation (translate_ruleset Γ) γ p (rule_translation { matchExpr := m, action := a }) initial_register ?regs1
    · apply rule_evaluation.elist_nomatch
      exact l1_nomatch γ p m initial_register hyp_match
    -- ⊢ { verdict := Verdict.NFT_CONTINUE, destination_chain := initial_register.destination_chain }.verdict =
    -- Verdict.NFT_CONTINUE
    · rfl
    -- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [])
    -- { verdict := Verdict.NFT_CONTINUE, destination_chain := initial_register.destination_chain }
    -- (let __src := initial_register;
    -- { verdict := Verdict.NFT_CONTINUE, destination_chain := __src.destination_chain })
    · exact ruleset_evaluation.skip
  case h.right =>
    exact simulation.undecided

theorem log_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(m : MatchExpr A) (hyp_match : matchExpression γ m p = true) :
∃ regs2,
  ruleset_evaluation (translate_ruleset Γ) γ p
    (ruleset_translation [{ matchExpr := m, action := Action.Log }])
    initial_register regs2
  ∧ simulation ProcessingDecision.undecided regs2 := by
  -- ⊢ ∃ regs2,
  -- ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Log }])
  -- initial_register regs2 ∧
  -- simulation ProcessingDecision.undecided regs2
  use { initial_register with verdict := Verdict.NFT_CONTINUE, destination_chain := none }
  apply And.intro
  case h.left =>
    apply ruleset_evaluation.nf_continue
    · rfl
    · apply rule_evaluation.elist_match
      exact l1_match γ p m initial_register hyp_match
    · rfl
    · exact ruleset_evaluation.skip
  case h.right =>
    exact simulation.undecided

theorem empty_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(m : MatchExpr A) (hyp_match : matchExpression γ m p = true) :
∃ regs2, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Empty }])
initial_register regs2 ∧ simulation ProcessingDecision.undecided regs2 := by
  use { initial_register with verdict := Verdict.NFT_CONTINUE, destination_chain := none }
  apply And.intro
  case h.left =>
    apply ruleset_evaluation.nf_continue
    · rfl
    · apply rule_evaluation.elist_match
      exact l1_match γ p m initial_register hyp_match
    · rfl
    · exact ruleset_evaluation.skip
  case h.right =>
    exact simulation.undecided

/- This is used in seq_equivalence_full (also I used it in call_return for rs1 ++ Return ++ rs2) to prove that translating rs1 ++ rs2 works.
    Evaluating a concatenation is the same evaluating sequentially with CONTINUE
    Given separate derivations for rs1 and rs2, construct a combined derivation
    for rs1++rs2-/
lemma ruleset_evaluation_append_continue
  -- rs1 evaluates regs1 -> regs_mid with Continue
  (H1 : ruleset_evaluation Γ γ p rs1 regs1 regs_mid)
  (hcont : regs_mid.verdict = Verdict.NFT_CONTINUE)
  -- rs2 evaluates regs2_mid -> regs12
  (H2 : ruleset_evaluation Γ γ p rs2 regs_mid regs2) :
  -- (rs1 ++ rs2) evaluates regs1 -> regs2
  ruleset_evaluation Γ γ p (rs1 ++ rs2) regs1 regs2 := by
  -- ⊢ ruleset_evaluation Γ γ p (rs1 ++ rs2) regs1 regs2
  -- ruleset_evuation is an inductive relation
  induction H1 generalizing regs2 with
  | skip => simpa using H2
  | nf_continue hcont_in rule_eval verdict_cont ruleset_eval ih =>
    have tail := ih hcont H2
    simpa using ruleset_evaluation.nf_continue hcont_in rule_eval verdict_cont tail
  -- contradiction for accept, drop, stolen, nf_return (used hammer for those)
  | accept => simp_all only [reduceCtorEq]
  | drop _ _ hv => simp_all only [reduceCtorEq]
  | stolen _ _ hv => simp_all only [reduceCtorEq]
  | nf_return _ _ hv =>  simp_all only [reduceCtorEq]
  | jump hcont_in hrule hvjump hdest hchain hchain_eval hrs_eval _ ih_rs =>
    have tail := ih_rs hcont H2
    simpa using ruleset_evaluation.jump hcont_in hrule hvjump hdest hchain hchain_eval tail
  | goto =>
    -- hvgoto says verdict = NFT_GOTO
    -- hcont says verdict = NFT_CONTINUE
    simp_all
    sorry
  -- goto is a tail-call; can't append after it (used hammer)
  | terminal ht => simp_all only [reduceCtorEq, or_self]

/-- If rs1 produces a terminal verdict, then rs1 ++ rs2 also produces the same result -/
lemma ruleset_evaluation_append_terminal {A P : Type} {Γ : NfRuleset A} {γ : Matcher A P} {p : P}
    {rs1 rs2 : List (Nftables.Rule A)} {regs1 regs_mid : Registers}
    (h1 : ruleset_evaluation Γ γ p rs1 regs1 regs_mid)
    (hterminal : regs_mid.verdict = Verdict.NFT_ACCEPT ∨ regs_mid.verdict = Verdict.NFT_DROP) :
    ruleset_evaluation Γ γ p (rs1 ++ rs2) regs1 regs_mid := by
  induction h1 with
  | skip => simp; exact ruleset_evaluation.terminal hterminal
  | nf_continue hcont_in rule_eval verdict_cont _ ih =>
    simpa using ruleset_evaluation.nf_continue hcont_in rule_eval verdict_cont (ih hterminal)
  | accept hcont hr hv => simpa using ruleset_evaluation.accept hcont hr hv
  | drop hcont hr hv => simpa using ruleset_evaluation.drop hcont hr hv
  | stolen hcont hr hv => simp_all  -- STOLEN is not ACCEPT or DROP
  | nf_return hcont hr hv => simp_all  -- RETURN is not ACCEPT or DROP
  | jump hcont hr hv hd hc hchain hrs _ ih_rs =>
    simpa using ruleset_evaluation.jump hcont hr hv hd hc hchain (ih_rs hterminal)
  | goto hcont hr hv hd hc hchain _ =>
    simp only [List.cons_append]
    exact ruleset_evaluation.goto hcont hr hv hd hc hchain
  | terminal ht => exact ruleset_evaluation.terminal ht

/-- T(rs1 ++ rs2) = T(rs1) ++ T(rs2)  -/
lemma rs_homomorphism (rs1 rs2 : List (Iptables.Rule A)) :
    ruleset_translation (rs1 ++ rs2) =
    ruleset_translation rs1 ++ ruleset_translation rs2 := by
  induction rs1 with
  | nil => rfl
  | cons r rs h =>
    simp only[ruleset_translation, List.cons_append, h]

/-- simulation undecided implies NFT_CONTINUE verdict -/
lemma simrel_undecided_continue {regs : Registers}
    (h : simulation ProcessingDecision.undecided regs) :
    regs.verdict = Verdict.NFT_CONTINUE := by
  cases h
  rfl

-- the translated nftables evaluation of rs starting from regs gives
-- a state regs1 related to iptables decision t
def nf_eval_produces {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
    (rs : List (Iptables.Rule A)) (regs_in : Registers) (t_out : ProcessingDecision) : Prop :=
  ∃ regs_out, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation rs) regs_in regs_out
    ∧ simulation t_out regs_out

/- If you run rs1 and rs2 sequentially in iptables, the translated
nftables gives the same results. -/
theorem seq_equivalence_full {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(rs1 rs2 : List (Iptables.Rule A)) (t : ProcessingDecision)

/- For any regs_in that's undecided -> evaluating rs1 stays undecided -/
(H1 : ∀ regs_in, simulation ProcessingDecision.undecided regs_in ->
  nf_eval_produces Γ γ p rs1 regs_in ProcessingDecision.undecided)

/- For any regs_mid that's undecided -> evaluating rs2 gives decision t -/
(H2 : ∀ regs_mid, simulation ProcessingDecision.undecided regs_mid ->
  nf_eval_produces Γ γ p rs2 regs_mid t)

(regs : Registers) (simrel : simulation ProcessingDecision.undecided regs) :

/- There exist some regs_out, such that evaluating the translated rs1 ++ rs2
   from regs gives regs_out, and it satisfies the relation with decision t -/
∃ regs_out, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation (rs1 ++ rs2)) regs regs_out
∧ simulation t regs_out := by
  -- ⊢ ∃ regs_out,
  -- ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation (rs1 ++ rs2)) regs regs_out
  -- ∧ simulation t regs_out
  unfold nf_eval_produces at H1
  unfold nf_eval_produces at H2
  have ⟨regs_mid, rs_eval1, int_sim⟩ := H1 regs simrel
  have ⟨regs_out, rs_eval2, fin_sim⟩ := H2 regs_mid int_sim
  have mid_verdict : regs_mid.verdict = Verdict.NFT_CONTINUE := simrel_undecided_continue int_sim
  rw [rs_homomorphism]
  use regs_out
  constructor
  case h.left => exact ruleset_evaluation_append_continue rs_eval1 mid_verdict rs_eval2
  case h.right => exact fin_sim


theorem skip_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
  (t : ProcessingDecision) (regs : Registers) (sim : simulation t regs) :
  ∃ regs', ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation []) regs regs'
  ∧ simulation t regs' := by
  simp [ruleset_translation]
  exact ⟨regs, ruleset_evaluation.skip, sim⟩

theorem decision_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
    (rs : List (Iptables.Rule A)) (X : Iptables.FinalDecision) (regs : Registers)
    (sim : simulation (ProcessingDecision.decision X) regs) :
    ∃ regs', ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation rs) regs regs'
    ∧ simulation (ProcessingDecision.decision X) regs' := by
    have terminal : regs.verdict = Verdict.NFT_ACCEPT ∨ regs.verdict = Verdict.NFT_DROP := by
      cases sim with
      | allow =>
        left
        rfl
      | deny =>
        right
        rfl
    exact ⟨regs, ruleset_evaluation.terminal terminal, sim⟩


/--If an iptables Call rule's match expression succeds on a packet,
then the translated nftables rule evaluates successfullt,
producing the result of an applying a Jump statement-/
lemma call_rule_eval {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(m : MatchExpr A) (chain : String) (hyp_match : matchExpression γ m p = true) :
rule_evaluation (translate_ruleset Γ) γ p (rule_translation { matchExpr := m, action := Action.Call chain })
initial_register (apply_statement (Statement.Jump chain) initial_register) := by
-- l1_match : iptables match success -> nftables expressions match
-- rule_evaluation.elist_match: expressions match -> rule evaluates
  exact rule_evaluation.elist_match (l1_match γ p m initial_register hyp_match)

lemma return_rule_eval {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
    (m : MatchExpr A) (regs : Registers) (hyp_match : matchExpression γ m p = true) :
    rule_evaluation (translate_ruleset Γ) γ p
      (rule_translation {matchExpr := m, action := Action.Return})
      regs (apply_statement Statement.Return regs) := by
  exact rule_evaluation.elist_match (l1_match γ p m regs hyp_match)

/-- If iptables calls a chain and that chain hits a Return, then the
  nftables translation produces undecided.

  Jump logic (reminder):
  - rules eval before call in main chain
  - hit Call chain -> jump into the called chain
  -- evaluate rs1 (stay undecided)
  - hit Return and exit the called chain
  -- rs2 is never reached
  -- back to the main chain -/
theorem call_return_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(m : MatchExpr A) (chain : String)

(rs1 : List (Iptables.Rule A)) (m1 : MatchExpr A) (rs2 : List (Iptables.Rule A))
-- the call rule in the main chain
(hyp_match : matchExpression γ m p = true)

-- rs1: rules before return
-- rs2: rules after return (never executed)
-- the called chain is split into: rs1 ++ [Return rule with m'] ++ rs2
(hyp_chain : Γ chain = some (rs1 ++ [{ matchExpr := m1, action := Action.Return }] ++ rs2))
-- the return rule in the main chain (proof that it fires)
(hyp_match1 : matchExpression γ m1 p = true)

-- assumption that rs1 preserves undecided decision
(IH_rs1 : ∀ regs_in, simulation ProcessingDecision.undecided regs_in ->
    nf_eval_produces Γ γ p rs1 regs_in ProcessingDecision.undecided) :

--  call chain (which contains rs1 + Return + rs2 produces undecided)
nf_eval_produces Γ γ p  [{ matchExpr := m, action := Action.Call chain }]
initial_register ProcessingDecision.undecided := by
  -- the Call rule translates correctly
  have h_rule := call_rule_eval Γ γ p m chain hyp_match
  -- need the proof that the rule fires
  -- need proof that the chain evaluates
  -- rs1 ++ [Return rule] ++ rs2
  -- proof of how jump converts return -> continue
  -- rs1 evaluates from initial_register to regs_int, staying in undecided
  have ⟨regs_int, rs_eval1, sim_int⟩ := IH_rs1 initial_register simulation.undecided

  -- registers after evaluating es1
  have regs_mid : regs_int.verdict = Verdict.NFT_CONTINUE := simrel_undecided_continue sim_int

  -- return rule fires from regs_int
  have rule_return := return_rule_eval Γ γ p m1 regs_int hyp_match1

  -- registers after return rule
  let regs_return := apply_statement Statement.Return regs_int
  have regs_return_pf : regs_return.verdict = Verdict.NFT_RETURN :=
     -- ⊢ regs_return.verdict = Verdict.NFT_RETURN
  rfl

  -- [Return] ++ rs2 evaluates from regs_int to regs_return, rs2 is skipped
  have ret_rs2 : ruleset_evaluation (translate_ruleset Γ) γ p
    (rule_translation {matchExpr := m1, action := Action.Return} :: ruleset_translation rs2)
    regs_int regs_return := by
    -- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p
    -- (rule_translation { matchExpr := m1, action := Action.Return }
    -- :: ruleset_translation rs2) regs_int regs_return
    exact ruleset_evaluation.nf_return regs_mid rule_return regs_return_pf

  -- rs1 ++ [Return] ++ rs2
  have final_eval : ruleset_evaluation (translate_ruleset Γ) γ p
    (ruleset_translation (rs1 ++ [{matchExpr := m1, action := Action.Return}] ++ rs2))
    initial_register regs_return := by
  -- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p
  -- (ruleset_translation (rs1 ++ [{ matchExpr := m1, action := Action.Return }] ++ rs2)) initial_register regs_return
    repeat rw [rs_homomorphism]
  -- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p
  -- (ruleset_translation rs1 ++ ruleset_translation [{ matchExpr := m1, action := Action.Return }] ++
  -- ruleset_translation rs2)
  -- initial_register regs_return

  -- List.append_assoc - lemma
  -- @[simp]
  -- theorem List.append_assoc{α : Type u} (as bs cs : List α) :
  -- as ++ bs ++ cs = as ++ (bs ++ cs)
    simp [List.append_assoc]
  -- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p
  --(ruleset_translation rs1 ++
  -- (ruleset_translation [{ matchExpr := m1, action := Action.Return }] ++ ruleset_translation rs2))
  -- initial_register regs_return
    apply ruleset_evaluation_append_continue
    --⊢ H1: ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation rs1) initial_register ?regs_mid
    -- hcont: ⊢ Registers.verdict ?regs_mid = Verdict.NFT_CONTINUE
    -- H2: ⊢ ruleset_evaluation (translate_ruleset Γ) γ p
    -- regs_mid : ⊢ Registers
    case H1 =>
      exact rs_eval1
    case hcont =>
      exact regs_mid
    case H2 =>
       exact ret_rs2

    -- jump statement regs
  let regs1 := apply_statement (Statement.Jump chain) initial_register
  have jump_regs : regs1.verdict = Verdict.NFT_JUMP := by
    exact rfl
  have jump_dest_chain : regs1.destination_chain = some chain := by
      exact rfl

  have chain_lookup : (translate_ruleset Γ) chain = some
   (ruleset_translation (rs1 ++ [{ matchExpr := m1, action := Action.Return}] ++ rs2)) := by
  -- ⊢ translate_ruleset Γ chain = some (ruleset_translation (rs1 ++ [{ matchExpr := m1, action := Action.Return }] ++ rs2))
    unfold translate_ruleset
  -- ⊢ Option.map ruleset_translation (Γ chain) =
  -- some (ruleset_translation (rs1 ++ [{ matchExpr := m1, action := Action.Return }] ++ rs2))
    rw [hyp_chain]
  -- ⊢ Option.map ruleset_translation (some (rs1 ++ [{ matchExpr := m1, action := Action.Return }] ++ rs2)) =
  -- some (ruleset_translation (rs1 ++ [{ matchExpr := m1, action := Action.Return }] ++ rs2))
    rfl

  -- since rest is never happens
  have rest_eval : ruleset_evaluation (translate_ruleset Γ) γ p []
    {verdict := Verdict.NFT_CONTINUE, destination_chain := none}
    {verdict := Verdict.NFT_CONTINUE, destination_chain := none} := by
    exact ruleset_evaluation.skip

  -- ⊢ nf_eval_produces Γ γ p [{ matchExpr := m, action := Action.Call chain }] initial_register ProcessingDecision.undecided
  unfold nf_eval_produces
  -- ⊢ ∃ regs_out, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Call chain }])
  -- initial_register regs_out ∧ simulation ProcessingDecision.undecided regs_out
  use initial_register
  -- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Call chain }])
  -- initial_register initial_register ∧
  -- simulation ProcessingDecision.undecided initial_register
  apply And.intro
  case h.left =>
    exact ruleset_evaluation.jump rfl h_rule jump_regs jump_dest_chain chain_lookup final_eval rest_eval
  case h.right =>
    exact simulation.undecided

theorem call_result_equivalence {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
  (m : MatchExpr A) (chain : String) (rs : List (Iptables.Rule A)) (t : ProcessingDecision)
  (hyp_match : matchExpression γ m p = true)
  (hyp_chain : Γ chain = some rs)
  (IH_chain : ∀ regs_in, simulation ProcessingDecision.undecided regs_in ->
    nf_eval_produces Γ γ p rs regs_in t) :

  nf_eval_produces Γ γ p [{ matchExpr := m, action := Action.Call chain }] initial_register t := by
  -- ⊢ nf_eval_produces Γ γ p [{ matchExpr := m, action := Action.Call chain }] initial_register t
  unfold nf_eval_produces
  -- ⊢ ∃ regs_out, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Call chain }]) initial_register regs_out ∧
  -- simulation t regs_out
  -- the jump rule fires, producing regs1 (verdict=NFT_JUMP, destination = chain)
  have rule_pf := call_rule_eval Γ γ p m chain hyp_match
  -- ⊢ ∃ regs_out, ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Call chain }])
  -- initial_register regs_out ∧
  -- simulation t regs_out
  -- called chain rs evaluates from initial_register to a corresponding to a decision t in nftables
  have chain_pf : nf_eval_produces Γ γ p rs initial_register t :=
  IH_chain initial_register simulation.undecided
  unfold nf_eval_produces at chain_pf

  obtain ⟨regs_out, chain_eval, sim⟩ := chain_pf

  let regs1 := apply_statement (Statement.Jump chain) initial_register
  have jump_regs : regs1.verdict = Verdict.NFT_JUMP := by rfl
  have jump_dest : regs1.destination_chain = some chain := by rfl
  have chain_lookup : (translate_ruleset Γ) chain = some (ruleset_translation rs) := by
  -- ⊢ translate_ruleset Γ chain = some (ruleset_translation rs)
    unfold translate_ruleset
  -- ⊢ Option.map ruleset_translation (Γ chain) = some (ruleset_translation rs)
    rw [hyp_chain]
    rfl

  -- ⊢ ∃ regs_out,
  -- ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Call chain }])
  -- initial_register regs_out ∧
  -- simulation t regs_out
  cases sim
  -- case undecided: chain_eval : ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation rs) initial_register
  -- { verdict := Verdict.NFT_CONTINUE, destination_chain := none }
  -- case allow : ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation rs) initial_register
  -- { verdict := Verdict.NFT_ACCEPT, destination_chain := none }
  -- case deny:
  -- chain_eval : ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation rs) initial_register
  -- { verdict := Verdict.NFT_DROP, destination_chain := none }
  case undecided =>
    use initial_register
    apply And.intro
    -- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m, action := Action.Call chain }])
    -- initial_register initial_register
    exact ruleset_evaluation.jump rfl rule_pf jump_regs jump_dest chain_lookup chain_eval ruleset_evaluation.skip
    exact simulation.undecided
  case allow =>
    use {verdict := Verdict.NFT_ACCEPT, destination_chain := none}
    apply And.intro
    exact ruleset_evaluation.jump rfl rule_pf jump_regs jump_dest chain_lookup chain_eval ruleset_evaluation.skip
    exact simulation.allow
  case deny =>
    use {verdict := Verdict.NFT_DROP, destination_chain := none}
    apply And.intro
    exact ruleset_evaluation.jump rfl rule_pf jump_regs jump_dest chain_lookup chain_eval ruleset_evaluation.skip
    exact simulation.deny



-- if iptables evaluates rs from state t to state t',
-- and the nftables register regs correspond to t (via simulation),
-- then the translated rules evalouate in nftables from regs
-- to some regs', that corresponds to t'
theorem forward_simulation {A P : Type} (Γ : Ruleset A) (γ : Matcher A P) (p : P)
(rs : List (Iptables.Rule A)) (t t' : ProcessingDecision) (ipt_eval: iptables_bigstep Γ γ p rs t t')
(regs : Registers) (sm : simulation t regs) :
∃ regs', ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation rs) regs regs' ∧
simulation t' regs' := by
--proof by derivation on iptables (ech iptables_bigstep const)
induction ipt_eval generalizing regs with
-- in each case, need to connect sm : simulation with the corresponding _equivalence lemma

-- | accept {m} : matchExpression γ m p = true ->
  -- iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Accept }]
  -- ProcessingDecision.undecided (ProcessingDecision.decision FinalDecision.allow)

  /- If the match succeds, a single Accept rule takes iptables
  from undecided to allow
  -/
  | accept =>
    have regs_eq : regs = initial_register := by
      cases sm
      rfl
    rw[regs_eq]
    exact accept_equivalence Γ γ p _ ‹_›

  | drop =>
  /- ⊢ ∃ regs',
  ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation [{ matchExpr := m✝, action := Action.Drop }]) regs
      regs' ∧
    simulation (ProcessingDecision.decision Iptables.FinalDecision.deny) regs'
  -/
    have regs_eq : regs = initial_register := by
      cases sm
      rfl

    rw[regs_eq]
    exact drop_rej_equivalence Γ γ p _ ‹_›

  | reject =>
    have regs_eq : regs = initial_register := by
      cases sm
      rfl

    rw[regs_eq]
    exact drop_rej_equivalence Γ γ p _ (by assumption)

  | skip =>
    exact skip_equivalence Γ γ p _ regs sm

  | log =>
    have regs_eq : regs = initial_register := by
      cases sm
      rfl
    rw[regs_eq]
    exact log_equivalence Γ γ p _ (by assumption)

  | empty =>
    have regs_eq : regs = initial_register := by
      cases sm
      rfl
    rw[regs_eq]
    exact empty_equivalence Γ γ p _ (by assumption)

  | decision =>
    exact decision_equivalence Γ γ p _ _ regs sm

  | noMatch =>
    /- noMatch {m a} : matchExpression γ m p = false →
    iptables_bigstep Γ γ p [{matchExpr := m, action := a}] undecided undecided
  -/
    have regs_eq : regs = initial_register := by
      cases sm
      rfl
    rw[regs_eq]
    exact noMatch_equivalence Γ γ p _ _ (by assumption)

  | seq =>
    rename_i rs1 rs2 t1 t2 ev1 ev2 H1 H2
    have regs_eq : regs = initial_register := by
      cases sm
      rfl
    rw [regs_eq]

    cases t1 with
    | undecided =>
      exact seq_equivalence_full Γ γ p rs1 rs2 t2 (fun regs sim => H1 regs sim) (fun regs sim => H2 regs sim) initial_register simulation.undecided
    | decision d =>
      /- ⊢ ∃ regs',
      -- ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation (rs1 ++ rs2)) initial_register regs' ∧
      -- simulation t2 regs' -/
      have ⟨regs_mid, rs_eval1, sim_mid⟩ := H1 initial_register simulation.undecided
      cases ev2 with -- pattern matches iptables derivation for rs2
        | skip =>
          -- rs1 + [] = rs1
          simp [List.append_nil]
          subst regs_eq
          simp_all only
        | decision =>
          have terminal : regs_mid.verdict = Verdict.NFT_ACCEPT ∨ regs_mid.verdict = Verdict.NFT_DROP := by
            cases sim_mid with
              | allow =>
                left
                rfl
              | deny =>
                right
                rfl
          /-⊢ ∃ regs',
          ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation (rs1 ++ rs2)) initial_register regs' ∧
          simulation (ProcessingDecision.decision d) regs'-/
          use regs_mid
          /- ⊢ ruleset_evaluation (translate_ruleset Γ) γ p (ruleset_translation (rs1 ++ rs2)) initial_register regs_mid ∧
          simulation (ProcessingDecision.decision d) regs_mid-/
          constructor
          case h.left =>
            rw [rs_homomorphism]
            exact ruleset_evaluation_append_terminal rs_eval1 terminal
          case h.right =>
            exact sim_mid

  | call_return =>
    /-| call_return {m chain rs₁ m' rs₂} :
    matchExpression γ m p = true →            -- (1) call rule matches
    Γ chain = some (rs₁ ++ [{m', Return}] ++ rs₂) →  -- (2) chain structure
    matchExpression γ m' p = true →           -- (3) return rule matches
    iptables_bigstep Γ γ p rs₁ undecided undecided →  -- (4) rs₁ stays undecided
    iptables_bigstep Γ γ p [{m, Call chain}] undecided undecided
    -/
    rename_i m1 chain rs1 m2 rs2 hyp_match1 hyp_chain hyp_match2 eval H1
    have regs_eq : regs = initial_register := by
      cases sm
      rfl
    rw [regs_eq]
    have hlpr := call_return_equivalence Γ γ p m1 chain rs1 m2 rs2 hyp_match1 hyp_chain hyp_match2
      (fun regs_in sim => H1 regs_in sim)

    -- hammer
    subst regs_eq
    simp_all only [List.append_assoc, List.cons_append, List.nil_append]
    exact hlpr

  | call_result =>
    rename_i m chain rs1 t hyp_match hyp_chain eval1 H1
    /-
    | call_result {m chain rs t} :
    matchExpression γ m p = true →
    Γ chain = some rs →
    iptables_bigstep Γ γ p rs undecided t →
    iptables_bigstep Γ γ p [{ matchExpr := m, action := Action.Call chain }] undecided t
-/
  -- set regs = initial_register
    have regs_eq : regs = initial_register := by
      cases sm
      rfl
    rw [regs_eq]
    have hlpr := call_result_equivalence Γ γ p _ _ _ _ hyp_match hyp_chain
      (fun regs_in sim => H1 regs_in sim)

    -- hammer
    subst regs_eq
    exact hlpr
