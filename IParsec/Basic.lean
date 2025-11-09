inductive IndentationRel : Type where
  | Eq : IndentationRel
  | Gt : IndentationRel
  | Ge : IndentationRel
  | Any : IndentationRel

def ParseError : Type := String

abbrev Indentation : Type := Int


def maxInd : Indentation := 1000

structure IndentationState : Type where
  min : Indentation
  max : Indentation
  absMode : Bool
  rel : IndentationRel

def initialIndentationState : IndentationState :=
  { min := 0, max := maxInd, absMode := False, rel := IndentationRel.Any}

structure State  : Type  where
  input : String
  indent : IndentationState

inductive Consumed (a : Type) : Type where
  | Consumed : a → Consumed a
  | Empty : a → Consumed a

inductive Reply (a : Type) : Type where
  | Ok : a → State → Reply a
  | Error : ParseError → Reply a

structure Parsec (a : Type) : Type where
  run : (State → Consumed (Reply a))

/--
Modify the state the parser is run in.
-/
def modifyState {a : Type}(f : State → State)(p : Parsec a) : Parsec a :=
  Parsec.mk (λ s => p.run (f s))

def parsec_bind {a b : Type} :
   Parsec a →
   (a -> Parsec b) →
   Parsec b :=
   open Reply in
   λ ma f => Parsec.mk (λ s =>
     match ma.run s with
     | Consumed.Consumed (Ok a s') => (f a).run s'
     | Consumed.Consumed (Error err) => (Consumed.Consumed (Error err))
     | Consumed.Empty (Ok a s') => (f a).run s'
     | Consumed.Empty (Error err) => Consumed.Empty (Error err)
     )

instance parsecMonad : Monad Parsec where
  pure := λ x => Parsec.mk (λ s => Consumed.Empty (Reply.Ok x s))
  bind := parsec_bind

/--
Sets the indentation relation for the next token.
Corresponds to `p^rel` in the paper.
-/
def localIndentation {a : Type}(rel : IndentationRel)(p : Parsec a) : Parsec a := sorry

/--
Corresponds to `|p|` in the paper.
-/
def absoluteIndentation {a : Type}(p : Parsec a) : Parsec a := sorry

/--
Sets the default indentation mode that is applied to all tokens to the given indentation relation.
-/
def localTokenMode {a : Type}(rel : IndentationRel)(p : Parsec a) : Parsec a :=
  modifyState (λ ⟨input, indents⟩ => State.mk input {indents with  rel := rel }) p

def charP (c : Char) : Parsec Unit :=
  Parsec.mk (λ s => match s.input.toList with
                    | List.nil => Consumed.Empty (Reply.Error "input is empty")
                    | List.cons x xs => if x == c
                                        then Consumed.Consumed (Reply.Ok Unit.unit ⟨String.mk xs, s.indent⟩)
                                        else Consumed.Consumed (Reply.Error "Character doesn't match")
                    )


def parse (input : String) (parser : Parsec a) : Option a :=
  let initialState : State := { input := input, indent := initialIndentationState }
  match parser.run initialState with
  | Consumed.Consumed (Reply.Ok res _) => some res
  | Consumed.Empty (Reply.Ok res _) => some res
  | _ => none


def aab_parser : Parsec Unit := do
  charP 'a'
  charP 'a'
  charP 'b'

#guard parse "" (charP 'a') == none
#guard parse "a" (charP 'a') == some Unit.unit
#guard parse "b" (charP 'a') == none
#guard parse "aab" aab_parser == some Unit.unit
#guard parse "bba" aab_parser == none
