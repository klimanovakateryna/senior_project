import IptablesSemantics.iptables.syntax
open Iptables

namespace Nftables

/--Verdict codes in nftables.-/
inductive Verdict
| NFT_ACCEPT
| NFT_DROP
| NFT_CONTINUE
| NFT_BREAK
| NFT_JUMP
| NFT_GOTO
| NFT_RETURN
| NFT_STOLEN
deriving DecidableEq

structure Registers where
  verdict : Verdict
  destination_chain : Option String

/-- Initial register state-/
def initial_register : Registers :=
  {verdict := Verdict.NFT_CONTINUE, destination_chain := none}

/-- Check if verdict is terminal (ACCEPT or DROP) -/
def is_terminal : Verdict -> Bool
  | Verdict.NFT_ACCEPT => true
  | Verdict.NFT_DROP => true
  | Verdict.NFT_STOLEN => true
  | _ => false

inductive Expression (A : Type) where
  | Comparison (m : MatchExpr A)

inductive Statement where
  | Accept
  | Drop
  | Jump (chain : String)
  | Goto (chain : String)
  | Return
  | Continue
  deriving BEq

inductive RuleStatement (A : Type) where
 | SingleStatement (statement : Statement)
 | MapLookup (mapName : String) (m : A)

inductive SideEffect where
  | Log
  | Counter
  | Limit
  | Dnat
  | Snat
  | Masquerade
  deriving BEq

/-- Convert Statement to Verdict and optional destination chain -/
def statement_to_verdict : Statement -> (Verdict × Option String)
  | Statement.Accept => (Verdict.NFT_ACCEPT, none)
  | Statement.Drop => (Verdict.NFT_DROP, none)
  | Statement.Jump chain => (Verdict.NFT_JUMP, some chain)
  | Statement.Goto chain => (Verdict.NFT_GOTO, some chain)
  | Statement.Return => (Verdict.NFT_RETURN, none)
  | Statement.Continue => (Verdict.NFT_CONTINUE, none)

/-- Rule structure: [expr1, expr, ..] statement-/
structure Rule (A : Type) where
  expressions : List (Expression A)
  sideEffects : List SideEffect
  statement : RuleStatement A

/-Maps-/
abbrev NfMap (A : Type) := List (A × Statement)
abbrev NfLookup (A : Type) := String -> Option (NfMap A)

end Nftables
