inductive DBType where
  | int
  | string
  | bool

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool

#eval ("Fuck" : DBType.string.asType)

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec

structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2 :: cols) -- product types are right associative

abbrev Table (s : Schema) := List (Row s)

abbrev peak : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"elevation", .int⟩,
  ⟨"lastVisited", .int⟩
]

def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]

abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]

def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]

def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ => match r1, r2 with
    | (v1, r1'), (v2, r2') => v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq

#eval DBType.int

inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
    HasCol bigger n t →
    Subschema smaller bigger →
    Subschema (⟨n, t⟩ :: smaller) bigger

abbrev travelDiary : Schema := 
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]

example : Subschema travelDiary peak := by repeat constructor

def Subschema.addColumn (sub : Subschema smaller bigger) : Subschema smaller (c :: bigger) :=
  match sub with
  | .nil => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

