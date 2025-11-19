import IParsec.Definition
import IParsec.Combinators

def aab_parser : Parsec Char Unit := do
  tokenP 'a'
  tokenP 'a'
  tokenP 'b'

def a_or_b_parser : Parsec Char Unit := or (backtrack (tokenP 'a')) (tokenP 'b')


#guard parse "" (tokenP 'a') == none
#guard parse "a" (tokenP 'a') == some Unit.unit
#guard parse "b" (tokenP 'a') == none
#guard parse "aab" aab_parser == some Unit.unit
#guard parse "bba" aab_parser == none
#guard parse "a" a_or_b_parser == some Unit.unit
#guard parse "b" a_or_b_parser == some Unit.unit
#guard parse "" (many (tokenP 'a')) == some []
#guard parse "aa" (many (tokenP 'a')) == some [Unit.unit, Unit.unit]
#guard parse "" (many1 (tokenP 'a')) == none
#guard parse "aa" (many1 (tokenP 'a')) == some [Unit.unit, Unit.unit]
