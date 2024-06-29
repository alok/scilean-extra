@[simp] theorem map_data (f : α → β) (arr : Array α) : (arr.map f).data = arr.data.map f := by
  rw [Array.map, Array.mapM_eq_foldlM]
  apply congrArg Array.data (Array.foldl_eq_foldl_data (fun bs a => bs.push (f a)) #[] arr) |>.trans
  have H (l arr) : List.foldl (fun (bs: Array _) a => bs.push (f a)) arr l = ⟨arr.data ++ l.map f⟩ := by
    induction l generalizing arr <;> simp [*]
  simp [H]


instance : Functor Array where
  map := Array.map

instance : LawfulFunctor List where
  id_map := by simp [Functor.map]
  comp_map := by simp [Functor.map]
  map_const := by simp [Functor.mapConst, Functor.map]

#synth LawfulFunctor List
/-
Array.map_data.{u_2, u_1} {α : Type u_1} {β : Type u_2} (f : α → β) (arr : Array α) :
  (Array.map f arr).data = List.map f arr.data

  -- can use injectivity for proof
-/

theorem Array.map_id  (xs : Array α) : Array.map id xs = xs := by
  -- take .data of both lhs and rhs
  apply congrArg Array.data (Array.foldl_eq_foldl_data (fun bs a => bs.push a) #[] xs)
  rw [map_data]
  simp [List.map_id]
  rw [Array.map, Array]
  apply congrArg Array.data (Array.foldl_eq_foldl_data (fun bs a => bs.push a) #[] xs) |>.trans
  simp [List.foldl]
  rw [← map_data (f := id) (arr := xs)]
  simp [id]

instance : LawfulFunctor Array where
  id_map : ∀ {α : Type u_1} (x : Array α), id <$> x = x := by
    -- intro α x
    simp [Functor.map, Array.mapM, map_data,  map_data]
    -- apply congrArg Array.mk
    -- simp [map_data]
    -- exact @LawfulFunctor.id_map List _ x.data

  comp_map := by
    intros α β γ g h x
    simp [Functor.map, Array.map]
    apply congrArg Array.mk
    rw [map_data, map_data, map_data]
    exact LawfulFunctor.comp_map g h x.data

  map_const := by
    intros α β b x
    simp [Functor.mapConst, Functor.map, Array.map]
    apply congrArg Array.mk
    rw [map_data]
    exact LawfulFunctor.map_const b x.data
