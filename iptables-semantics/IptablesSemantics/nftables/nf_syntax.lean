import IptablesSemantics.iptables.syntax
open Iptables

namespace Nftables

/--Verdict codes used in nftables.
   These represent the possible outcomes of rule evaluation.-/
inductive Verdict
| NFT_ACCEPT   -- terminal: accept packet
| NFT_DROP     -- terminal: drop packet
| NFT_CONTINUE -- non-terminal: continue to next rule
| NFT_BREAK    -- internal: comparison failed, skip rest of rule
| NFT_JUMP     -- control flow: jump to chain (with return)
| NFT_GOTO     -- control flow: goto chain (no return)
| NFT_RETURN   -- control flow: return from chain
| NFT_STOLEN   -- terminal: packet consumed
deriving DecidableEq

/-- Registers store the current verdict state during evaluation.
    Based on kernel's nft_regs and nft_verdict structures. -/
structure Registers where
  verdict : Verdict
  destination_chain : Option String

/-- Initial register state: CONTINUE with no destination -/
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

/-- Statements are actions performed when a rule's expressions match.
    They determine the final verdict. -/
inductive Statement where
  | Accept                        -- NFT_ACCEPT
  | Drop                          -- NFT_DROP
  | Jump (chain : String)         -- NFT_JUMP to chain
  | Goto (chain : String)         -- NFT_GOTO to chain
  | Return                        -- NFT_RETURN
  | Continue                      -- NFT_CONTINUE (proceed to next rule)

/-- Convert Statement to Verdict and optional destination chain -/
def statement_to_verdict : Statement -> (Verdict × Option String)
  | Statement.Accept => (Verdict.NFT_ACCEPT, none)
  | Statement.Drop => (Verdict.NFT_DROP, none)
  | Statement.Jump chain => (Verdict.NFT_JUMP, some chain)
  | Statement.Goto chain => (Verdict.NFT_GOTO, some chain)
  | Statement.Return => (Verdict.NFT_RETURN, none)
  | Statement.Continue => (Verdict.NFT_CONTINUE, none)

/-- An nftables rule: a list of expressions followed by a statement.
    Rule structure: [expr1, expr2, ...] → statement -/
structure Rule (A : Type) where
  expressions : List (Expression A)
  statement : Statement

end Nftables
