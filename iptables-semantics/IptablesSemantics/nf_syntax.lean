import IptablesSemantics.syntax
open Firewall

namespace Nftables

/--Verdict statements -/
inductive Verdict
| NFT_ACCEPT -- absolute verdict
| NFT_DROP -- absolute verdict
| NFT_JUMP
| NFT_GOTO
| NFT_CONTINUE
| NFT_RETURN
| NFT_BREAK

/-- Temporary memory locations used to store the verdict state.
Derived from:
struct nft_regs {
	union {
		u32			data[NFT_REG32_NUM];
		struct nft_verdict	verdict;
	};
};

struct nft_verdict {
	u32				code;
	struct nft_chain		*chain; -- @chain: destination chain for NFT_JUMP/NFT_GOTO
};

 -/
structure Registers where
  verdict : Verdict
  destination_chain : Option String

/-- Initial register state. Starting verdict is set to CONTINUE, destination chain is set to NONE-/
def r : Registers := {verdict := Verdict.NFT_CONTINUE, destination_chain := (none : Option String) }

/--Returns true if ACCEPT or DROP, otherwise FALSE-/
def is_decided : Verdict -> Bool
  | Verdict.NFT_ACCEPT => true
  | Verdict.NFT_DROP => true
  | _ => false

  /--Expressions-/
inductive Expression (A : Type) where
  | Compare (primitive : A) -- nft_cmp: sets BREAK if fails
  | setVerdict (v: Verdict) (chain : Option String)

/--Rules in nftables contain expression lists-/
structure Rule (A : Type) where
  expressions : List (Expression A)

end Nftables
