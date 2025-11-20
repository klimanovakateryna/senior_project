import IptablesSemantics.syntax
import IptablesSemantics.decision_state
import IptablesSemantics.semantics

open Firewall

inductive primitive
| Protocol (protocol : String)
| SourceIP (ip : String)
| DestIP (ip : String)
| DestPort (port : Nat)
