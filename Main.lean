import «ScileanExtra»
import LeanColls
import SciLean.Data.DataArray
-- import SciLean.Data.ArrayType
import Lean.Parser
import SciLean.Data.DataArray
import SciLean.Data.EnumType
import Lean

open SciLean
open Lean

def Array.length (xs: Array a): ℕ := xs.size



-- syntax:10 (name := lxor) term:10 " LXOR " term:11 : term
-- -- run the function given at the end for each element of the list
-- syntax "foreach " "[" term,* "]" term : term

-- syntax "idk" : tactic
-- macro_rules
--   | `(tactic| idk) => `(tactic| omega)
-- example : 11  = 33 /3 := by idk







-- check we didn't mess up Lean's indexing syntax where a proof can be provided with a `'`.
variable (a' : Array Nat) (i j : Fin a'.size)

-- #check a'[i]
-- #check a'[:i]
-- #check a'[i:]
-- #check a'[i:j]


/-- hacky way of getting `[Repr α]` morally-/
def Axes := List ((α : Type) × EnumType α × Repr α)




namespace SciLean

  /---length of list of shapes-/
class NDIndex (ι : Type _) extends IndexType ι where
  /-- individual dimensions-/
  dims: Array Nat
  -- dims : Fin rank → Nat



instance : NDIndex (Idx n) where
  card := n
  toFin := id
  fromFin := id

  dims := fun _ => n.toNat

instance [inst : NDIndex ι] : NDIndex (Idx n × ι) where
  rank := inst.rank + 1
  dims := fun i =>
    match i with
    | ⟨0,_⟩ => n.toNat
    | ⟨n+1,_⟩ => inst.dims ⟨n, sorry⟩

class NDArray  [PlainDataType a] [IndexType idx] extends (DataArrayN a idx) where
  shape: NDIndex idx

end SciLean


abbrev Scalar := Float
structure Vector (rows: Nat) where
  data: Array Scalar
deriving Repr,BEq

structure Matrix (rows: Nat) (cols: Nat) where
  -- may as well use the iso between vector and matrix to build up
  data: Vector (rows * cols)
deriving Repr,BEq
def Vector.numel (xs: Vector rows): Nat := xs.data.size
def Matrix.numel (xs: Matrix rows cols): Nat := xs.data.numel

def Vector.map (f: Scalar -> Scalar) (v : Vector rows) : Vector rows := ⟨v.data.map f⟩
def Vector.zipWith  (xs: Vector rows) (ys: Vector rows) (f: Scalar -> Scalar -> Scalar)   : Vector rows := ⟨xs.data.zipWith ys.data f⟩
def Matrix.map (f: Scalar -> Scalar) (xs: Matrix rows cols): Matrix rows cols := ⟨xs.data.map f⟩
def Matrix.zipWith   (xs: Matrix rows cols) (ys: Matrix rows cols) (f: Scalar -> Scalar -> Scalar): Matrix rows cols := ⟨xs.data.zipWith ys.data f⟩
def Vector.get (vec: Vector rows) (i: Fin vec.data.size): Scalar := vec.data.get i
def testVector: Vector 2 := ⟨#[1.0,2.0]⟩
def testMatrix: Matrix 2 2 :=  ⟨⟨#[1.0,2.0,3.0,4.0]⟩⟩


-- TODO ask on zulip if way to auto gen instance for commutative op
/-- Scalar multiplication for Matrix. -/
instance : HMul Scalar (Matrix rows cols) (Matrix rows cols) where
  hMul scalar matrix := ⟨matrix.data.map (· * scalar)⟩

instance : HMul (Matrix rows cols) Scalar (Matrix rows cols) where
  hMul matrix scalar := scalar * matrix

#eval  2.0 * testMatrix * 0.5 == testMatrix

/-- Scalar multiplication for Vector. -/
instance : HMul Scalar (Vector rows) (Vector rows) where
  hMul scalar vector := ⟨vector.data.map (· * scalar)⟩



-- instance : Repr (Matrix rows cols) where
--   reprPrec xs p := Id.run do
--     let mut s := "Matrix\n"
--     for r in [:rows] do
--       for c in [:cols] do

--       s := s ++ "\n"
--     s

-- #eval (⟨#[1.0,2.0,3.0,4.0]⟩:Matrix 2 2)



instance : NDIndex (Fin rows) where
  dims := #[rows]
-- cont idx elem dom

-- instance : GetElem (Array α) Nat α fun xs i => LT.lt i xs.size where
--   getElem xs i h := xs.get ⟨i, h⟩

instance : GetElem (Matrix rows cols) (Fin rows) Scalar (fun xs i => i < xs.numel) where
  getElem xs i h := xs.data.data.get ⟨↑i, h⟩

instance : GetElem (Matrix rows cols) Nat Scalar (fun xs i => i < xs.numel) where
  getElem xs i h := xs.data.data.get ⟨i, h⟩

instance : GetElem (Matrix rows cols) (Nat × Nat) Scalar (fun xs (r,c) => c+r*cols < xs.data.size) where
  getElem xs i h := Id.run do
    let (r,c) := i
    xs.data.data.get ⟨c+r*cols, h⟩

instance  : Add  (Matrix rows cols) where
  add xs ys := ⟨xs.data.zipWith ys.data (·+·)⟩

instance : Sub (Matrix rows cols) where
  sub xs ys := ⟨xs.data.zipWith ys.data (·-·)⟩

/-- Instance for getting an element from a Vector by a natural number index. -/
instance : GetElem (Vector rows) Nat Float (fun xs i => i < xs.data.size) where
  getElem xs i h := xs.data.get ⟨i, h⟩

/-- Instance for adding two Vectors. -/
instance : Add (Vector rows) where
  add xs ys := ⟨xs.data.zipWith ys.data (·+·)⟩

/-- Instance for subtracting one Vector from another. -/
instance : Sub (Vector rows) where
  sub xs ys := ⟨xs.data.zipWith ys.data (·-·)⟩

/-- Instance for scalar multiplication of a Vector. -/
instance : HMul (Vector rows) Float (Vector rows) where
  hMul xs scalar := ⟨xs.data.map (·*scalar)⟩

/-- Instance for scalar division of a Vector. -/
instance : HDiv (Vector rows) Float (Vector rows) where
  hDiv xs scalar := ⟨xs.data.map (·/scalar)⟩

instance : HMul (Matrix rows cols) Float (Matrix rows cols) where
  hMul mat scalar := ⟨mat.data.map (· * scalar)⟩

-- works over any commutative scalars, so whatever
instance : HMul Float (Matrix rows cols) (Matrix rows cols) where
  hMul scalar mat := mat * scalar

#eval testMatrix * 2.0
#eval 2.0 * testMatrix

instance : Mul (Matrix rows cols) where
  mul xs ys := Id.run do
    let mut result := Array.mkArray (rows * cols) 0.0
    for r in [:rows] do
      for c in [:cols] do
        let mut sum := 0.0
        for k in [:cols] do
          sum := sum + xs.data.get ⟨r * cols + k, omega⟩ * ys.data.get ⟨k * cols + c, sorry⟩
        result := result.set ⟨r * cols + c, sorry⟩ sum
    ⟨⟨result⟩⟩



#eval testMatrix + testMatrix
#eval testMatrix - testMatrix
#eval testMatrix * testMatrix


#eval testMatrix[1,1]
#eval testMatrix[0]
#eval testMatrix[(0: Fin 2)]!
-- #eval (: Fin 3)
instance : NDIndex (Fin rows × Fin cols) where
  dims := #[rows, cols]
#eval testMatrix[]
instance [NDIndex idx] : SciLean.NDArray (Matrix rows cols) idx where
  shape := inferInstance


instance : HMul (Matrix rows cols) (Vector cols) (Vector rows) where
  hMul mat vec := Id.run do
    let mut result := Array.mkArray rows 0.0
    for r in [:rows] do
      for c in [:cols] do
        result := result.set ⟨r, sorry⟩ (result.get ⟨r, sorry⟩ + mat.data.get ⟨r * cols + c, sorry⟩ * vec.data.get ⟨c, sorry⟩)
    ⟨result⟩


instance : HDiv (Vector rows) Float (Vector rows) where
  hDiv xs scalar := ⟨xs.data.map (· / scalar)⟩

/-- abs taken by mathlib -/
def abs' (x: Float): Float := if x < 0 then -x else x

def Array.maxBy (xs: Array α) (f: α → Float): Float := xs.foldl (fun acc x => max acc (f x)) 0.0
def Vector.maxAbs (xs: Vector rows): Float := xs.data.maxBy (fun x => abs' x)

#eval testMatrix * testVector
-- Performs power iteration to approximate the dominant eigenvalue and its corresponding eigenvector of a matrix.
--
-- # Arguments
-- - `mat`: The matrix for which to find the dominant eigenvalue and eigenvector.
-- - `maxIterations`: The maximum number of iterations to perform. Defaults to 1000.
-- - `tolerance`: The tolerance for convergence. Defaults to 1e-10.
--
-- # Returns
-- A tuple containing the approximated dominant eigenvalue and its corresponding eigenvector.

def Matrix.full (rows cols) (a: Float) : Matrix rows cols := ⟨Array.mkArray (rows*cols) a⟩

def Matrix.fullLike (xs: Matrix rows cols) (fillVal:Float): Matrix rows cols := ⟨Array.mkArray (rows*cols) fillVal⟩

def Matrix.zerosLike (xs: Matrix rows cols) := xs.fullLike 0.0
def Matrix.onesLike (xs: Matrix rows cols) := xs.fullLike 1.0
def Vector.norm (xs: Vector rows): Float := .sqrt <| xs.data.foldl (fun acc x => acc + x*x) 0.0

def Vector.distance (xs: Vector rows) (ys: Vector rows): Float := (xs - ys).norm

#eval testVector.norm
#eval testVector.distance testVector

def powerIteration (mat : Matrix rows rows) (maxIterations : Nat := 1000) (tolerance : Float := 1e-10) : (Float × Vector rows) := Id.run do

  let mut eigenVector: Vector rows := ⟨Array.mkArray rows 1.0⟩ -- Start with a guess for the eigenvector
  let mut eigenValue := 0.0
  let mut prevEigenValue := eigenValue
  for _ in [:maxIterations] do
    let tempVector := mat * eigenVector -- Multiply the matrix by the vector
    eigenValue := tempVector.norm -- The eigenvalue approximation is the norm of the result
    eigenVector := tempVector / eigenValue -- Normalize the vector
    if abs' (eigenValue - prevEigenValue) < tolerance then
      break -- Convergence achieved
    prevEigenValue := eigenValue
  (eigenValue, eigenVector)

#eval powerIteration testMatrix
#eval powerIteration testMatrix.onesLike

def SciLean.DataArrayN.parseAxes [PlainDataType α] [Index idx] (xs: DataArrayN α idx) (s:String) : Except String Axes := do
  dbg_trace s
  let words := extractUniqueWords s
  let axes:Axes := _
  if axes.length != words.length then
    .error "some axes not match"
  else
    .ok axes

-- parseEin array "i " = [Idx array.size]
-- parseEin array "i j" = [Idx array.size, Idx array.size]

def xs := ⊞[0., 1.]
-- instance Coe String StrippedString where -- strip whitespace automatically with Coe
#check_failure xs.parseAxes "a -> a a"
#eval parseAxes "a"



def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
