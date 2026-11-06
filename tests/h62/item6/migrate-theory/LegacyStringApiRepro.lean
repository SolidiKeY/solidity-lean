import Lean

/-! Negative control: these exact API shapes from Syntax.Raw must elaborate on
4.24 and fail on 4.35. This file is intentionally excluded from library roots. -/
namespace H62.MigrateTheory.LegacyStringApiRepro

def dropped (s : String) : String := s.drop 1
def chars (s : String) : List Char := (s.drop 1).toList
def trimmed (s : String) : String := s.dropRight 1
def suffix (s : String) : Option String := ["[]memory", "[]storage"].find? s.endsWith

end H62.MigrateTheory.LegacyStringApiRepro
