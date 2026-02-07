import IParsec.Definition

def new_indentation_set (s : IndentationState) (r : IndentationRel) : IndentationState :=
  match s.set with
  | IndentationSet.Any => {s with set := IndentationSet.Any }
  | IndentationSet.Exact i =>
    match r with
    | IndentationRel.Any => {s with set := IndentationSet.Any}
    | IndentationRel.Eq => {s with set := IndentationSet.Exact i}
    | IndentationRel.Ge => {s with set := IndentationSet.Min i}
    | IndentationRel.Gt => {s with set := IndentationSet.Min (i + 1)}
  | IndentationSet.Min i =>
    match r with
    | IndentationRel.Any => {s with set := IndentationSet.Any}
    | IndentationRel.Eq => {s with set := IndentationSet.Min i}
    | IndentationRel.Ge => {s with set := IndentationSet.Min i}
    | IndentationRel.Gt => {s with set := IndentationSet.Min (i + 1)}

/--
Sets the indentation relation for the next token.
Corresponds to `p^rel` in the paper.
-/
def localIndentation {tok α : Type}
                     (rel : IndentationRel)
                     (p : Parsec tok α)
                     : Parsec tok α := do
    let s ← getState
    let new := new_indentation_set s.indent rel
    putState { s with indent := new }
    p


def setAbsoluteIndentation {tok : Type}(s : State tok) : State tok :=
  let indent := s.indent
  { input := s.input
    indent := { indent with absMode := true }
  }

/--
Corresponds to `|p|` in the paper.
-/
def absoluteIndentation {tok α : Type}
                        (p : Parsec tok α)
                        : Parsec tok α :=
  modifyState setAbsoluteIndentation p


/--
Sets the default indentation mode that is applied to all tokens to the given indentation relation.
-/
def localTokenMode {tok α : Type}
                   (rel : IndentationRel)
                   (p : Parsec tok α)
                   : Parsec tok α :=
  modifyState (λ ⟨input, indents⟩ => State.mk input {indents with  rel := rel }) p

/--
Pop the next token from the input.
This consumes the token and returns an error if the input is empty.
-/
def pop { tok : Type} : Parsec tok (Veriflex.Located tok) :=
  λ s => match s.input with
          | List.nil => Consumed.Empty (Reply.Error "Input is empty")
          | List.cons x xs => Consumed.Consumed (Reply.Ok x ⟨xs, s.indent⟩)

/--
Peek at the next token from the input.
This doesn't consume the token and returns an error if the input is empty.
-/
def peek { tok : Type} : Parsec tok (Veriflex.Located tok) :=
  λ s => match s.input with
          | List.nil => Consumed.Empty (Reply.Error "Input is empty")
          | List.cons x xs => Consumed.Empty (Reply.Ok x ⟨x :: xs, s.indent⟩)

/--
Asserts that the property `p` holds and throws the given error otherwise.
-/
def assert {tok : Type} (p : Bool)(err : ParseError) : Parsec tok Unit :=
  λ s => if p
         then Consumed.Empty (Reply.Ok Unit.unit s)
         else Consumed.Empty (Reply.Error err)

def check_valid_indent (s : IndentationState)
                       (i : Indentation) : Bool :=
  match s.set with
  | IndentationSet.Any => true
  | IndentationSet.Exact i' => i = i'
  | IndentationSet.Min i' => i' ≤ i

/--
A parser that immediately fails without consuming any input.
-/
def fail {tok α : Type} : Parsec tok α :=
  λ _ => Consumed.Empty (Reply.Error "fail")

/--
Parse a single token.
-/
def tokenP{tok : Type}[BEq tok](c : tok) : Parsec tok Unit := do
  let tok ← pop
  let s ← getState
  assert (tok.content == c) "Character doesn't match"
  assert (check_valid_indent s.indent tok.location) "Indentation is wrong"
  let new_indent := {s.indent with set := IndentationSet.Exact tok.location}
  putState { s with indent := new_indent }

/--
Parses and returns a single token if it satisfies the given predicate.
-/
def satisfyP{tok α : Type}(p : tok → Option α) : Parsec tok α := do
  let tok ← pop
  let s ← getState
  let new_indent := {s.indent with set := IndentationSet.Exact tok.location}
  putState { s with indent := new_indent }
  match p tok.content with
  | none => λ _ => Consumed.Consumed (Reply.Error "satisfyP: Predicate not satisfied")
  | some r => pure r


def backtrack{tok α : Type}(p : Parsec tok α) : Parsec tok α :=
  λ s => match p s with
        | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
        | Consumed.Consumed (Reply.Error err) => Consumed.Empty (Reply.Error err)
        | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
        | Consumed.Empty (Reply.Error err) => Consumed.Empty (Reply.Error err)



/-- Left-biased or-combinator which doesn't backtrack -/
def or {tok α: Type}(p₁ p₂ : Parsec tok α): Parsec tok α :=
  λ s => match p₁ s with
          | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
          | Consumed.Consumed (Reply.Error err) => Consumed.Consumed (Reply.Error err)
          | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
          | Consumed.Empty (Reply.Error _) => p₂ s


/--
Left-biased or-combinator which doesn't backtrack.
A generalization of the `or` combinator.
-/
def ors{tok α : Type}(ps : List (Parsec tok α)) : Parsec tok α :=
  List.foldr or fail ps


partial def many{tok α : Type}(p : Parsec tok α) : Parsec tok (List α) :=
  let f : Parsec tok (List α) := do
    let x ← p
    let xs ← many p
    pure (x :: xs)
  or f (pure [])

def many1{α : Type}(p : Parsec tok α) : Parsec tok (List α) := do
  let x ← p
  let xs ← many p
  pure (x :: xs)
