import ScileanExtra
import LeanColls
import SciLean.Data.DataArray
import Lean.Parser
import SciLean.Data.EnumType
import Lean
import SciLean.Data.ArrayType

open SciLean

open Lean
namespace SciLean'

variable {Cont : Type _} {Idx : Type _ |> outParam} {Elem : Type _ |> outParam}
variable {Idx : Type _} [IndexType Idx] [LawfulIndexType Idx] [DecidableEq Idx]

-- NaN is > all values
private instance : Ord Float where
  compare x y := if x < y then .lt else if x == y then .eq else .gt


/-- A Float for ease-/
abbrev Scalar := Float
/-- Returns the length of an array. -/
def Array.length (xs : Array α) : ℕ := xs.size

/-- Represents axes with their associated type, enumeration, and representation. -/
def Axes (a : Type) := List (a : Type) × EnumType a × Repr a

/-- A class representing an N-dimensional index. -/
class NDIndex (idx : Type _) extends IndexType idx where
  /-- The dimensions of the index.
  - [ ] make it a `Vector`
  -/
  dims : Array Nat
/-- A class representing an N-dimensional array. -/
class NDArray [PlainDataType a] [IndexType idx] extends DataArrayN a idx where
  shape : NDIndex idx

/-- Represents a vector with a specified number of rows. -/
structure Vector (n : Nat) (Scalar : Type := Float) where
  data : Array Scalar
  deriving Repr, BEq

/-- Represents a matrix with specified rows and columns. -/
structure Matrix (rows : Nat) (cols : Nat) where
  data : Vector (rows * cols)
  deriving Repr, BEq

/-- Returns the number of elements in a vector. -/
def Vector.numel (xs : Vector n) : Nat := xs.data.size

/-- Returns the number of elements in a matrix. -/
def Matrix.numel (xs : Matrix rows cols) : Nat := xs.data.numel


instance : Functor (Vector n ·) where
  map f xs := ⟨xs.data.map f⟩

/-- Notation for constructing a vector with inferred size. -/
syntax "vec[" sepBy(term, ", ") "]" : term


/-- Macro expansion for vector notation. -/
macro_rules
| `(vec[$elems:term,*]) => do
  `((Vector $elems.getElems.size).mk #[ $elems,* ])

#eval vec[1, 2, 3, 4]
/-- Applies a function to each element of a vector. -/
def Vector.map (f : Scalar → Scalar) (v : Vector n) : Vector n := Functor.map f v
#eval vec[1, 2].map (.)
/-- Combines two vectors element-wise using a specified function. -/
def Vector.zipWith (xs : Vector n) (ys : Vector n) (f : Scalar → Scalar → Scalar) : Vector n := ⟨xs.data.zipWith ys.data f⟩

/-- Applies a function to each element of a matrix. -/
def Matrix.map (f : Scalar → Scalar) (xs : Matrix rows cols) : Matrix rows cols := ⟨xs.data.map f⟩

/-- Combines two matrices element-wise using a specified function. -/
def Matrix.zipWith (xs : Matrix rows cols) (ys : Matrix rows cols) (f : Scalar → Scalar → Scalar) : Matrix rows cols := ⟨xs.data.zipWith ys.data f⟩

/-- Retrieves an element from a vector by its index. -/
def Vector.get (vec : Vector n) (i : Fin vec.data.size) : Scalar := vec.data.get i

/-- Example vector for testing. -/
def testVector : Vector 2 := ⟨#[1.0, 2.0]⟩

/-- Example matrix for testing. -/
def testMatrix : Matrix 2 2 := ⟨⟨#[1.0, 2.0, 3.0, 4.0]⟩⟩


/-- Scalar multiplication for matrices. -/
instance : HMul Scalar (Matrix rows cols) (Matrix rows cols) where
  hMul scalar matrix := ⟨matrix.data.map (· * scalar)⟩

instance : HMul (Matrix rows cols) Scalar (Matrix rows cols) where
  hMul matrix scalar := scalar * matrix

#eval 2.0 * testMatrix * 0.5 == testMatrix

/-- Scalar multiplication for vectors. -/
instance : HMul Scalar (Vector n) (Vector n) where
  hMul scalar vector := ⟨vector.data.map (· * scalar)⟩

instance : GetElem (Matrix rows cols) (Fin rows) Scalar (fun xs i => i < xs.numel) where
  getElem xs i h := xs.data.data.get ⟨↑i, h⟩

instance : GetElem (Matrix rows cols) Nat Scalar (fun xs i => i < xs.numel) where
  getElem xs i h := xs.data.data.get ⟨i, h⟩

instance : GetElem (Matrix rows cols) (Nat × Nat) Scalar (fun xs (r, c) => c + r * cols < xs.data.numel) where
  getElem xs rc h := Id.run do
    let (r,c) := rc
    return xs.data.data.get ⟨c + r * cols, h⟩


#eval testMatrix[1, 1]
instance : Add (Matrix rows cols) where
  add xs ys := ⟨xs.data.zipWith ys.data (· + ·)⟩

instance : Sub (Matrix rows cols) where
  sub xs ys := ⟨xs.data.zipWith ys.data (· - ·)⟩

instance : GetElem (Vector rows) Nat Float (fun xs i => i < xs.data.size) where
  getElem xs i h := xs.data.get ⟨i, h⟩

instance : Add (Vector rows) where
  add xs ys := ⟨xs.data.zipWith ys.data (· + ·)⟩

instance : Sub (Vector rows) where
  sub xs ys := ⟨xs.data.zipWith ys.data (· - ·)⟩

instance : HMul (Vector rows) Float (Vector rows) where
  hMul xs scalar := ⟨xs.data.map (· * scalar)⟩

instance : HDiv (Vector rows) Float (Vector rows) where
  hDiv xs scalar := ⟨xs.data.map (· / scalar)⟩

instance : HMul (Matrix rows cols) Float (Matrix rows cols) where
  hMul mat scalar := ⟨mat.data.map (· * scalar)⟩

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

#eval testMatrix[1, 1]
#eval testMatrix[0]
#eval testMatrix[(0 : Fin 2)]!

instance : NDIndex (Fin rows × Fin cols) where
  dims := #[rows, cols]

instance [NDIndex idx] : NDArray (Matrix rows cols) idx where
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


/-- Finds the maximum value in an array based on a provided function. -/
def _root_.Array.maxBy [Ord b] (xs: Array a) (f: a -> b) : Option b := xs.map f|>.max?
#eval #[1.0, 2.0, 3.0, 4.0].maxBy (· + 1)

def _root_.Array.max [Ord a] (xs: Array a) : Option a := xs.maxBy id
#eval #[1.0, 2.0, 3.0, 4.0].max

/-- Finds the maximum absolute value in a vector. -/
def Vector.maxAbs (xs : Vector rows) : Float := Id.run do
  let mut ans := xs[0]!
  for i in [1:rows] do
    if  xs[i]!.abs > ans then
      ans :=  xs[i]!.abs
  ans

#eval testMatrix * testVector
/-- Creates a matrix filled with a specified value. -/
def Matrix.full (rows cols) (a : Float) : Matrix rows cols := ⟨⟨Array.mkArray (rows * cols) a⟩⟩
/-- Creates a matrix filled with a specified value that matches the shape of the input matrix. -/
def Matrix.fullLike (_input : Matrix rows cols) (fillVal : Float := default) : Matrix rows cols := ⟨⟨Array.mkArray (rows * cols) fillVal⟩⟩

def Matrix.zerosLike (xs : Matrix rows cols) := xs.fullLike (fillVal := 0.0)
def Matrix.onesLike (xs : Matrix rows cols) := xs.fullLike (fillVal := 1.0)




/-- Surprisingly, Lean doesn't already have typeclass for Float^Nat-/
instance : HPow (Float) Nat Float where
  hPow x n := Id.run do
    let mut (acc, x, n) := (1.0, x, n)
    while n > 0 do
      if n % 2 = 0 then
        (x,n) := (x * x, n / 2)
      else
        (acc, x, n) := (acc * x, x * x, (n - 1) / 2)
    acc
#eval 2.2^(3:Nat)
#eval 1.0/3.
#eval 1/2.2
#eval ((2:Nat):Float)
#eval Nat.toFloat 3
#eval 1/((1).toFloat)
/-- The $L^p$-norm of a vector. -/
def Vector.pnorm (xs : Vector rows) (p : Nat := 2) : Float := xs.data.foldl (fun acc x => acc + (x.abs)^p) 0.0 |> .pow (1/p.toFloat)
/-- Calculates the norm of a vector. -/
def Vector.norm (xs : Vector rows) : Float := xs.pnorm (p:=2)
-- TODO debug 1 norm
#eval  (⟨#[1.0, 2.0]⟩: Vector 2).pnorm (p:=1)
#eval (2.2:Float)^(3:Nat)
/-- Calculates the distance between two vectors. -/
def Vector.distance (xs : Vector rows) (ys : Vector rows) : Float := (xs - ys).norm

def relu' [Max A] [OfNat A 0] (a:A) : A := max a 0

def Vector.relu (xs:Vector rows Scalar) :=(Functor.map relu' xs)

#eval testVector.norm
#eval testVector.distance testVector

/-- Performs power iteration to approximate the dominant eigenvalue and its corresponding eigenvector of a matrix. -/
def powerIteration (mat : Matrix rows rows) (maxIterations : Nat := 1000) (tolerance : Float := 1e-10) : (Float × Vector rows) := Id.run do
  let mut eigenVector : Vector rows := ⟨Array.mkArray rows 1.0⟩
  let mut eigenValue := 0.0
  let mut prevEigenValue := eigenValue
  for _ in [:maxIterations] do
    let tempVector := mat * eigenVector
    eigenValue := tempVector.norm
    eigenVector := tempVector / eigenValue
    if abs' (eigenValue - prevEigenValue) < tolerance then
      break
    prevEigenValue := eigenValue
  (eigenValue, eigenVector)

#eval powerIteration testMatrix
#eval powerIteration testMatrix.onesLike

def SciLean.DataArrayN.parseAxes [PlainDataType α] [Index idx] (xs : DataArrayN α idx) (s : String) : Except String Axes := do
  dbg_trace s
  let words := extractUniqueWords s
  let axes : Axes := _
  if axes.length != words.length then
    .error "some axes not match"
  else
    .ok axes

-- parseEin array "i " = [Idx array.size]
-- parseEin array "i j" = [Idx array.size, Idx array.size]


def Vector.range (start :Float := 0.0) (end' :Float := 100.0) (step :Float := 1.0) : Vector ((end' - start) / step) := ⟨Array.mkArray ((end' - start) / step) start⟩
/--
  Computes the floor of a floating-point number to the nearest integer,
  returning it as a natural number.
  - [ ] make work, the ints are arbitrary precision. may require dipping into C++
-/
def Float.toInt (x : Float) : Int := sorry



/--
  Generates a range vector from `start` to `end'` with a step size of `step`,
  using floor division to ensure the size is a natural number.
-/
def Vector.range (start : Float := 0.0) (end' : Float := 100.0) (step : Float := 1.0) : Vector (floorToNat ((end' - start) / step)) :=
  ⟨Array.mkArray (floorToNat ((end' - start) / step)) start⟩


namespace Micrograd

end Micrograd


-- instance Coe String StrippedString where -- strip whitespace automatically with Coe
-- Could use `Coe` to do data preprocessing since it defines a fixed pipeline
end SciLean'
def main : IO Unit :=
  IO.println s!"Hello, {hello}!"



namespace OrdFloat
end OrdFloat

#eval Float.isNaN (1/0 - 1/0)
#eval (1.0/0.0-1.0/0.0  )
