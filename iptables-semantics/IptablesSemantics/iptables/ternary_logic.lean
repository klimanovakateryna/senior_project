import IptablesSemantics.iptables.syntax

-- 6 Klenee logic
-- datatype ternaryvalue = TernaryTrue | TernaryFalse | TernaryUnknown
namespace KleeneLogic
open KleeneLogic
inductive ternaryvalue where
  | TernaryTrue
  | TernaryFalse
  | TernaryUnknown
  deriving BEq

inductive ternaryformula where
  | TernaryAnd : ternaryformula -> ternaryformula -> ternaryformula
  | TernaryOr: ternaryformula -> ternaryformula -> ternaryformula
  | TernaryNot: ternaryformula -> ternaryformula
  | TernaryValue: ternaryvalue -> ternaryformula

/-Conversion from ternary to bool-/
/-fun ternary-to-bool :: ternaryvalue ⇒bool option where
ternary-to-bool TernaryTrue= Some True |
ternary-to-bool TernaryFalse= Some False |
ternary-to-bool TernaryUnknown= None-/
def ternary_to_bool : ternaryvalue -> Option Bool
  | ternaryvalue.TernaryTrue => some true
  | ternaryvalue.TernaryFalse => some false
  | ternaryvalue.TernaryUnknown => none

/-Conversion from bool to ternary-/
/-fun bool-to-ternary :: bool ⇒ternaryvalue where
bool-to-ternary True= TernaryTrue |
bool-to-ternary False= TernaryFalse
-/
def bool_to_ternary : Bool -> ternaryvalue
| true => ternaryvalue.TernaryTrue
| false => ternaryvalue.TernaryFalse

/-Ternary AND
-/
/-fun eval-ternary-And :: ternaryvalue ⇒ternaryvalue ⇒ternaryvalue where
eval-ternary-And TernaryTrue TernaryTrue= TernaryTrue |
eval-ternary-And TernaryTrue TernaryFalse= TernaryFalse |
eval-ternary-And TernaryFalse TernaryTrue= TernaryFalse |
eval-ternary-And TernaryFalse TernaryFalse= TernaryFalse |
eval-ternary-And TernaryFalse TernaryUnknown= TernaryFalse |
eval-ternary-And TernaryTrue TernaryUnknown= TernaryUnknown |
eval-ternary-And TernaryUnknown TernaryFalse= TernaryFalse |
eval-ternary-And TernaryUnknown TernaryTrue= TernaryUnknown |
eval-ternary-And TernaryUnknown TernaryUnknown= TernaryUnknown-/

def eval_ternary_And : ternaryvalue -> ternaryvalue -> ternaryvalue
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryTrue => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryFalse => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryTrue => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryFalse => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryUnknown
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryFalse => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryTrue => ternaryvalue.TernaryUnknown
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryUnknown

/-fun eval-ternary-Or :: ternaryvalue ⇒ternaryvalue ⇒ternaryvalue where
eval-ternary-Or TernaryTrue TernaryTrue= TernaryTrue |
eval-ternary-Or TernaryTrue TernaryFalse= TernaryTrue |
eval-ternary-Or TernaryFalse TernaryTrue= TernaryTrue |
eval-ternary-Or TernaryFalse TernaryFalse= TernaryFalse |
eval-ternary-Or TernaryTrue TernaryUnknown= TernaryTrue |
eval-ternary-Or TernaryFalse TernaryUnknown= TernaryUnknown |
eval-ternary-Or TernaryUnknown TernaryTrue= TernaryTrue |
eval-ternary-Or TernaryUnknown TernaryFalse= TernaryUnknown |
eval-ternary-Or TernaryUnknown TernaryUnknown= TernaryUnknown-/
def eval_ternary_Or : ternaryvalue -> ternaryvalue -> ternaryvalue
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryTrue => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryFalse => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryTrue => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryFalse => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryUnknown
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryFalse => ternaryvalue.TernaryUnknown
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryTrue => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryUnknown

/-fun eval-ternary-Not :: ternaryvalue ⇒ ternaryvalue where
eval-ternary-Not TernaryTrue= TernaryFalse |
eval-ternary-Not TernaryFalse= TernaryTrue |
eval-ternary-Not TernaryUnknown= TernaryUnknown-/
def eval_ternary_Not : ternaryvalue -> ternaryvalue
  | ternaryvalue.TernaryTrue => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryFalse => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryUnknown => ternaryvalue.TernaryUnknown

/-fun eval-ternary-Imp :: ternaryvalue ⇒ternaryvalue ⇒ternaryvalue where
74
eval-ternary-Imp TernaryTrue TernaryTrue= TernaryTrue |
eval-ternary-Imp TernaryTrue TernaryFalse= TernaryFalse |
eval-ternary-Imp TernaryFalse TernaryTrue= TernaryTrue |
eval-ternary-Imp TernaryFalse TernaryFalse= TernaryTrue |
eval-ternary-Imp TernaryTrue TernaryUnknown= TernaryUnknown |
eval-ternary-Imp TernaryFalse TernaryUnknown= TernaryTrue |
eval-ternary-Imp TernaryUnknown TernaryTrue= TernaryTrue |
eval-ternary-Imp TernaryUnknown TernaryFalse= TernaryUnknown |
eval-ternary-Imp TernaryUnknown TernaryUnknown= TernaryUnknown-/
def eval_ternary_Imp : ternaryvalue -> ternaryvalue -> ternaryvalue
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryTrue  => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryFalse  => ternaryvalue.TernaryFalse
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryTrue  => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryFalse  => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryTrue, ternaryvalue.TernaryUnknown  => ternaryvalue.TernaryUnknown
  | ternaryvalue.TernaryFalse, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryTrue => ternaryvalue.TernaryTrue
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryFalse => ternaryvalue.TernaryUnknown
  | ternaryvalue.TernaryUnknown, ternaryvalue.TernaryUnknown => ternaryvalue.TernaryUnknown

/-fun ternary-ternary-eval :: ternaryformula ⇒ternaryvalue where
76
ternary-ternary-eval (TernaryAnd t1 t2 ) = eval-ternary-And (ternary-ternary-eval
t1 ) (ternary-ternary-eval t2 ) |
ternary-ternary-eval (TernaryOr t1 t2 ) = eval-ternary-Or (ternary-ternary-eval
t1 ) (ternary-ternary-eval t2 ) |
ternary-ternary-eval (TernaryNot t) = eval-ternary-Not (ternary-ternary-eval t)
|
ternary-ternary-eval (TernaryValue t) = t-/
def ternary_ternary_eval : ternaryformula -> ternaryvalue
  | ternaryformula.TernaryAnd t1 t2 => eval_ternary_And (ternary_ternary_eval t1) (ternary_ternary_eval t2)
  | ternaryformula.TernaryOr t1 t2 => eval_ternary_Or (ternary_ternary_eval t1) (ternary_ternary_eval t2)
  | ternaryformula.TernaryNot t => eval_ternary_Not (ternary_ternary_eval t)
  | ternaryformula.TernaryValue t => t

/-definition ternary-eval :: ternaryformula ⇒bool option where
ternary-eval t= ternary-to-bool (ternary-ternary-eval t)-/
def ternary_eval : ternaryformula -> Option Bool
  | t => ternary_to_bool (ternary_ternary_eval t)

-- 7 Packet Matching with Ternary Logic

/-type-synonym (′a,′packet) exact-match-tac=′a ⇒′packet ⇒ternaryvalue-/
abbrev exact_match_tac (A P : Type) := A -> P -> ternaryvalue

/-type-synonym ′packet unknown-match-tac=action ⇒′packet ⇒bool-/
abbrev unknown_match_tac (DES P : Type) := DES -> P -> Bool

/-type-synonym (′a,unknown-match-tac)′packet) match-tac=((′a,′packet) exact-match-tac × ′packet unknown-match-tac)-/
abbrev match_tac (A DES P : Type) := exact_match_tac A P × unknown_match_tac DES P

/-fun map-match-tac :: (′a,
′packet) exact-match-tac ⇒′packet ⇒′a match-expr ⇒
ternaryformula where
map-match-tac β p (MatchAnd m1 m2 ) = TernaryAnd (map-match-tac β p m1 )
(map-match-tac β p m2 ) |
map-match-tac β p (MatchNot m) = TernaryNot (map-match-tac β p m) |
map-match-tac β p (Match m) = TernaryValue (β m p) |
map-match-tac - - MatchAny= TernaryValue TernaryTrue-/
def map_match_tac {A P : Type} (β : exact_match_tac A P) (p : P) : MatchExpr A -> ternaryformula
  | .MatchAnd m1 m2 => ternaryformula.TernaryAnd (map_match_tac β p m1) (map_match_tac β p m2)
  | .MatchNot m => ternaryformula.TernaryNot (map_match_tac β p m)
  | .Match m => ternaryformula.TernaryValue (β m p)
  | .MatchAny => ternaryformula.TernaryValue ternaryvalue.TernaryTrue

/- fun ternary-to-bool-unknown-match-tac :: ′packet unknown-match-tac ⇒action ⇒
′packet ⇒ternaryvalue ⇒bool where
ternary-to-bool-unknown-match-tac - - - TernaryTrue= True |
ternary-to-bool-unknown-match-tac - - - TernaryFalse= False |
ternary-to-bool-unknown-match-tac α a p TernaryUnknown= α a p -/
def ternary_to_bool_unknown_match_tac {DES P : Type} (α : unknown_match_tac DES P) (a : DES) (p : P) : ternaryvalue -> Bool
  | ternaryvalue.TernaryTrue => true
  | ternaryvalue.TernaryFalse => false
  | ternaryvalue.TernaryUnknown => α a p

/-definition matches :: (′a,
′packet) match-tac ⇒′a match-expr ⇒action ⇒′packet
⇒bool where
matches γm a p ≡ternary-to-bool-unknown-match-tac (snd γ) a p (ternary-ternary-eval
(map-match-tac (fst γ) p m))-/
def ternary_matches {A DES P : Type} (γ : match_tac A DES P) (m : MatchExpr A) (a : DES) (p : P) : Bool :=
  ternary_to_bool_unknown_match_tac γ.snd a p (ternary_ternary_eval (map_match_tac γ.fst p m))

/-(* Predicate: formula is in Negation Normal Form *)
inductive NegationNormalForm :: "ternaryformula ⇒ bool" where
  NegationNormalForm (TernaryValue v) |
  NegationNormalForm (TernaryNot (TernaryValue v)) |
  NegationNormalForm φ ⟹ NegationNormalForm ψ ⟹
    NegationNormalForm (TernaryAnd φ ψ) |
  NegationNormalForm φ ⟹ NegationNormalForm ψ ⟹
    NegationNormalForm (TernaryOr φ ψ) -/
inductive NegationNormalForm : ternaryformula -> Prop
  | TernaryValue : NegationNormalForm (ternaryformula.TernaryValue v)
  | TernaryNotValue : NegationNormalForm (ternaryformula.TernaryNot (ternaryformula.TernaryValue v))
  | TernaryAnd : NegationNormalForm φ -> NegationNormalForm ψ ->
    NegationNormalForm (ternaryformula.TernaryAnd φ ψ)
  | TernaryOr : NegationNormalForm φ -> NegationNormalForm ψ ->
    NegationNormalForm (ternaryformula.TernaryOr φ ψ)

/-(* Convert ternaryformula to NNF *)
fun NNF_ternary :: "ternaryformula ⇒ ternaryformula" where
  "NNF_ternary (TernaryValue v) = TernaryValue v" |
  "NNF_ternary (TernaryAnd t1 t2) = TernaryAnd (NNF_ternary t1) (NNF_ternary t2)" |
  "NNF_ternary (TernaryOr t1 t2) = TernaryOr (NNF_ternary t1) (NNF_ternary t2)" |
  "NNF_ternary (TernaryNot (TernaryNot t)) = NNF_ternary t" |
  "NNF_ternary (TernaryNot (TernaryValue v)) = TernaryValue (eval_ternary_Not v)" |
  "NNF_ternary (TernaryNot (TernaryAnd t1 t2)) =
    TernaryOr (NNF_ternary (TernaryNot t1)) (NNF_ternary (TernaryNot t2))" |
  "NNF_ternary (TernaryNot (TernaryOr t1 t2)) =
    TernaryAnd (NNF_ternary (TernaryNot t1)) (NNF_ternary (TernaryNot t2))" -/
def NNF_ternary : ternaryformula -> ternaryformula
  | ternaryformula.TernaryValue v => ternaryformula.TernaryValue v
  | ternaryformula.TernaryAnd t1 t2 => ternaryformula.TernaryAnd (NNF_ternary t1) (NNF_ternary t2)
  | ternaryformula.TernaryOr t1 t2 => ternaryformula.TernaryOr (NNF_ternary t1) (NNF_ternary t2)
  | ternaryformula.TernaryNot (ternaryformula.TernaryNot t) => NNF_ternary t
  | ternaryformula.TernaryNot (ternaryformula.TernaryValue v) => ternaryformula.TernaryValue (eval_ternary_Not v)
  | ternaryformula.TernaryNot (ternaryformula.TernaryAnd t1 t2) =>
    ternaryformula.TernaryOr (NNF_ternary (ternaryformula.TernaryNot t1)) (NNF_ternary (ternaryformula.TernaryNot t2))
  | ternaryformula.TernaryNot (ternaryformula.TernaryOr t1 t2) =>
    ternaryformula.TernaryAnd (NNF_ternary (ternaryformula.TernaryNot t1)) (NNF_ternary (ternaryformula.TernaryNot t2))

end KleeneLogic
