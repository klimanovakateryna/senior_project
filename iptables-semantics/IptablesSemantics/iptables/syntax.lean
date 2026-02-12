namespace Iptables

/-- Actions -/
inductive Action
| Accept
| Drop
| Log
| Reject
| Call (chain : String)
| Return
| Goto (chain : String)
| Empty
| Unknown
deriving BEq

end Iptables

/--Match expressions-/
inductive MatchExpr (A : Type)
| Match (a : A)
| MatchNot (m : MatchExpr A)
| MatchAnd(m1 m2 : MatchExpr A)
| MatchAny

/--Builds Or via De Morgan-/
def Iptables.matchOr {A} (m1 m2 : MatchExpr A) : MatchExpr A
  := MatchExpr.MatchNot (MatchExpr.MatchAnd (MatchExpr.MatchNot m1) (MatchExpr.MatchNot m2))

/--A firewall rule consists of a match experssion and an action-/
structure Iptables.Rule (A : Type) where
          matchExpr : MatchExpr A
          action : Action
