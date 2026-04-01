import Compcert.lib
import Compcert.archi
import Compcert.word

namespace Compcert
namespace floats

noncomputable section

/- Types for floating-point numbers and their payloads. -/

axiom float : Type
axiom float32 : Type
axiom nan_pl (w : Nat) : Type

instance : Inhabited float := ⟨sorry⟩
instance : Inhabited float32 := ⟨sorry⟩
instance : Inhabited (nan_pl w) := ⟨sorry⟩

/- The following operations are not implemented and use axioms. -/

axiom float_to_bits : float → Compcert.uword 64
axiom float_of_bits : Compcert.uword 64 → float
axiom float32_to_bits : float32 → Compcert.uword 32
axiom float32_of_bits : Compcert.uword 32 → float32

axiom float_is_nan : float → Bool
axiom float32_is_nan : float32 → Bool

axiom float_get_payload : float → nan_pl 53
axiom float32_get_payload : float32 → nan_pl 24

axiom float_is_signaling : nan_pl 53 → Bool
axiom float32_is_signaling : nan_pl 24 → Bool

axiom transform_quiet_pl (pl : nan_pl 53) : nan_pl 53

/- Nan payload operations for single <-> double conversions. -/

axiom expand_pl (pl : nan_pl 24) : nan_pl 53
axiom reduce_pl (pl : nan_pl 53) : nan_pl 24

def of_single_pl (s : Bool) (pl : nan_pl 24) : Bool × nan_pl 53 :=
(s, if Compcert.archi.float_of_single_preserves_sNaN
    then expand_pl pl
    else transform_quiet_pl (expand_pl pl))

def to_single_pl (s : Bool) (pl : nan_pl 53) : Bool × nan_pl 24 :=
(s, reduce_pl (transform_quiet_pl pl))

/- NaN payload operations for opposite and absolute value. -/

def neg_pl (s : Bool) (pl : nan_pl 53) := (!s, pl)
def abs_pl (s : Bool) (pl : nan_pl 53) := (false, pl)

axiom float_gen_nan (s : Bool) (pl : nan_pl 53) : float
axiom float32_gen_nan (s : Bool) (pl : nan_pl 24) : float32

/- Comparison and arithmetic operations. -/

inductive float_comparison
| FEq | FLt | FGt | FUn

axiom float_compare : float → float → Option float_comparison
axiom float32_compare : float32 → float32 → Option float_comparison

axiom float_unary_op : (float → float) → float → float
axiom float_binary_op : (float → float → float) → float → float → float

axiom float32_unary_op : (float32 → float32) → float32 → float32
axiom float32_binary_op : (float32 → float32 → float32) → float32 → float32 → float32

def float_neg (f : float) : float := sorry
def float_abs (f : float) : float := sorry
def float_add (f1 f2 : float) : float := sorry
def float_sub (f1 f2 : float) : float := sorry
def float_mul (f1 f2 : float) : float := sorry
def float_div (f1 f2 : float) : float := sorry

def float32_neg (f : float32) : float32 := sorry
def float32_abs (f : float32) : float32 := sorry
def float32_add (f1 f2 : float32) : float32 := sorry
def float32_sub (f1 f2 : float32) : float32 := sorry
def float32_mul (f1 f2 : float32) : float32 := sorry
def float32_div (f1 f2 : float32) : float32 := sorry

/- Conversions between floats and integers. -/

axiom float_of_int : Int → float
axiom float_of_uint : Nat → float
axiom float32_of_int : Int → float32
axiom float32_of_uint : Nat → float32

axiom float_to_int : float → Option Int
axiom float_to_uint : float → Option Nat
axiom float32_to_int : float32 → Option Int
axiom float32_to_uint : float32 → Option Nat

/- Conversions between float and float32. -/

axiom float_of_float32 : float32 → float
axiom float32_of_float : float → float32

/- Decidable equality. -/

axiom float_eq_dec : DecidableRel (@Eq float)
axiom float32_eq_dec : DecidableRel (@Eq float32)

instance : DecidableEq float := float_eq_dec
instance : DecidableEq float32 := float32_eq_dec

end

end floats
end Compcert
