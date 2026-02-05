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

end Iptables

/--Match expressions-/
inductive MatchExpr (A : Type) -- polimorphic type A, works for any type A
| Match (a : A) -- wraps a raw value of type A into a MatchExpr A
| MatchNot (m : MatchExpr A) -- logical negation, takes an existing match expression m of type MatchExpr A
| MatchAnd(m1 m2 : MatchExpr A) -- conjunction of two subexpressions, take two match expressions m1 and m2
| MatchAny -- an always true expression

/--Builds Or via De Morgan-/
def Iptables.matchOr {A} (m1 m2 : MatchExpr A) : MatchExpr A
  := MatchExpr.MatchNot (MatchExpr.MatchAnd (MatchExpr.MatchNot m1) (MatchExpr.MatchNot m2))

/--A firewall rule consists of a match experssion and an action-/
structure Iptables.Rule (A : Type) where
          matchExpr : MatchExpr A
          action : Action
