import IParsec.Definition
import IParsec.Combinators

def parse_string{α : Type} (input : String) (parser : Parsec Char α) : Option α :=
  let input := input.toList.map (λ x => ⟨0,x⟩)
  parse input  parser

def aab_parser : Parsec Char Unit := do
  tokenP 'a'
  tokenP 'a'
  tokenP 'b'

def a_or_b_parser : Parsec Char Unit := or (backtrack (tokenP 'a')) (tokenP 'b')

#guard parse_string "" (tokenP 'a') == none
#guard parse_string "a" (tokenP 'a') == some Unit.unit
#guard parse_string "b" (tokenP 'a') == none
#guard parse_string "aab" aab_parser == some Unit.unit
#guard parse_string "bba" aab_parser == none
#guard parse_string "a" a_or_b_parser == some Unit.unit
#guard parse_string "b" a_or_b_parser == some Unit.unit
#guard parse_string "" (many (tokenP 'a')) == some []
#guard parse_string "aa" (many (tokenP 'a')) == some [Unit.unit, Unit.unit]
#guard parse_string "" (many1 (tokenP 'a')) == none
#guard parse_string "aa" (many1 (tokenP 'a')) == some [Unit.unit, Unit.unit]
