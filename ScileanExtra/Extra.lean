
import LeanColls
import SciLean
namespace Extra

def intersperse {α : Type} (x : α) : List α → List α
| [] => []
| [a] => [a]
| a :: as => a :: x :: intersperse x as

#eval intersperse 0 [1,2]

def Array.intersperse (a : α) (xs : Array α) : Array α := Id.run do
  let mut out := #[]
  for x in xs do
    out := out |>.push x |>.push a
  return out


suggest_tactics "appending empty array is identity"

instance : Functor Array where
  map f xs := Id.run do
    let mut out := #[]
    for x in xs do
      out := out.push (f x)
    out

structure Vec (α : Type) (size: Nat) where
  data : Array α
  -- pf : data.size = size := sorry

instance : LawfulFunctor List where
  id_map xs := by
  comp_map f g xs := by cases xs <;> simp
  map_const := by tauto

-- theorem isEmpty_append : (l₁ ++ l₂ : List α).isEmpty ↔ l₁.isEmpty ∧ l₂.isEmpty := by cases l₁ <;> simp [List.isEmpty]


theorem isEmpty_iff_eq_nil {l : List α} : l.isEmpty ↔ l = [] := by cases l <;> simp [List.isEmpty ]--cases l with
--   | nil => simp_rw [List.isEmpty]
--   | cons a as => simp_rw [List.isEmpty]
-- -- <;> simp_rw [isEmpty]

theorem Array.isEmpty_iff_eq_nil {l : Array α} : l.isEmpty ↔ l = #[] := sorry

-- @[simp] theorem isEmpty_append : (l₁ ++ l₂ : Array α).isEmpty ↔ l₁.isEmpty ∧ l₂.isEmpty := by
--   repeat rw [isEmpty_iff_eq_nil]
--   suggest_tactics ""




-- instance : Monad Array where
--   pure x := #[x]
--   bind xs f := Id.run do
--     let mut out := #[]
--     for x in xs do
--       let sublist := f x
--       out := out ++ sublist
--     out



instance : LawfulFunctor Array where
  id_map xs := by simp_rw [Functor.map,Id.run, id, forIn,Array.forIn,Array.forIn.loop, Array.map, Id.run, Array.mapM, Array.mapM.map,Array.mkEmpty] --<;> rw [Array.map, Array.mapM] --suggest_tactics ""
  comp_map f g xs := by cases xs <;> simp [Functor.map]
  map_const := by tauto

end Extra
