namespace Iptables

/-- Final decision -/
inductive FinalDecision
 | allow
 | deny

/-- Processing decision -/
inductive ProcessingDecision
  | undecided
  | decision (d : FinalDecision) --take an argument d of type Final Decision and return as Processing Decision

end Iptables
