namespace Firewall

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

end Firewall

/--Match expressions-/
inductive MatchExpr (A : Type) -- polimorphic type A, works for any type A
| Match (a : A) -- wraps a raw value of type A into a MatchExpr A
| MatchNot (m : MatchExpr A) -- logical negation, takes an existing match expression m of type MatchExpr A
| MatchAnd(m1 m2 : MatchExpr A) -- conjunction of two subexpressions, take two match expressions m1 and m2
| MatchAny -- an always true expression

/--Builds Or via De Morgan-/
def Firewall.matchOr {A} (m1 m2 : MatchExpr A) : MatchExpr A
  := MatchExpr.MatchNot (MatchExpr.MatchAnd (MatchExpr.MatchNot m1) (MatchExpr.MatchNot m2))

/--A firewall rule consists of a match experssion and an action-/
structure Firewall.Rule (A : Type) where -- given A, define a type Rule A
          matchExpr : MatchExpr A
          action : Action
