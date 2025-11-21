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

/-- Tokens for the D² Dyck language -/
inductive Token : Type where
  | LParen : Token
  | RParen : Token
  | LBracket : Token
  | RBracket : Token
  deriving BEq

/-
The example from the paper:
A → ( `(` ; A> ; `)`  <|> `[`≥ ; A> ; `]`≥ )

- Matching parantheses must align vertically
- Things enclosed in parantheses must be aligned more to the right.
- Things enclosed in square brackets must be more indented than the surrounding code.
-
-/
mutual
  def parse_paren : Parsec Token Unit := do
    tokenP Token.LParen
    (localIndentation IndentationRel.Any (tokenP Token.RParen))

  def parse_bracket : Parsec Token Unit := do
    tokenP Token.LBracket
    tokenP Token.RBracket

  def parse_exp : Parsec Token Unit := do
    _ <- many (or parse_paren parse_bracket)
    return Unit.unit
end

#guard parse [⟨0,Token.LParen⟩,⟨1,Token.RParen⟩] parse_paren == some Unit.unit
#guard parse [] parse_exp == some Unit.unit
#guard parse [⟨0,Token.LParen⟩,⟨0,Token.RParen⟩] parse_exp == some Unit.unit
