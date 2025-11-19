import IParsec.Definition

/--
Sets the indentation relation for the next token.
Corresponds to `p^rel` in the paper.
-/
def localIndentation {tok α : Type}(rel : IndentationRel)(p : Parsec tok α) : Parsec tok α := sorry

/--
Corresponds to `|p|` in the paper.
-/
def absoluteIndentation {tok α : Type}(p : Parsec tok α) : Parsec tok α := sorry

/--
Sets the default indentation mode that is applied to all tokens to the given indentation relation.
-/
def localTokenMode {tok α : Type}(rel : IndentationRel)(p : Parsec tok α) : Parsec tok α :=
  modifyState (λ ⟨input, indents⟩ => State.mk input {indents with  rel := rel }) p

/--
Parse a single token.
-/
def tokenP{tok : Type}[BEq tok](c : tok) : Parsec tok Unit :=
  Parsec.mk (λ s => match s.input with
                    | List.nil => Consumed.Empty (Reply.Error "Input is empty")
                    | List.cons x xs => if x.content == c
                                        then Consumed.Consumed (Reply.Ok Unit.unit ⟨xs, s.indent⟩)
                                        else Consumed.Consumed (Reply.Error "Character doesn't match")
                    )

/--
Parses and returns a single token if it satisfies the given predicate.
-/
def satisfyP{tok : Type}(p : tok → Bool) : Parsec tok tok :=
  Parsec.mk (λ s => match s.input with
                    | List.nil => Consumed.Empty (Reply.Error "Input is empty")
                    | List.cons x xs => if p x.content
                                        then Consumed.Consumed (Reply.Ok x.content ⟨xs, s.indent⟩)
                                        else Consumed.Consumed (Reply.Error "Token does not satisfy predicate."))

def backtrack{tok α : Type}(p : Parsec tok α) : Parsec tok α :=
  Parsec.mk (λ s => match p.run s with
                    | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
                    | Consumed.Consumed (Reply.Error err) => Consumed.Empty (Reply.Error err)
                    | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
                    | Consumed.Empty (Reply.Error err) => Consumed.Empty (Reply.Error err)
                    )

/--
A parser that immediately fails without consuming any input.
-/
def fail {tok α : Type} : Parsec tok α :=
  Parsec.mk (λ _ => Consumed.Empty (Reply.Error "fail"))

/-- Left-biased or-combinator which doesn't backtrack -/
def or {tok α: Type}(p₁ p₂ : Parsec tok α): Parsec tok α :=
  Parsec.mk (λ s => match p₁.run s with
                    | Consumed.Consumed (Reply.Ok res s') => Consumed.Consumed (Reply.Ok res s')
                    | Consumed.Consumed (Reply.Error err) => Consumed.Consumed (Reply.Error err)
                    | Consumed.Empty (Reply.Ok res s') => Consumed.Empty (Reply.Ok res s')
                    | Consumed.Empty (Reply.Error _) => p₂.run s
  )

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
