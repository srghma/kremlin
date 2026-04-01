import Compcert.archi
import Compcert.lib
import Compcert.word

namespace Compcert
namespace integers
open Compcert.word

/- * Specialization to integers of size 8, 32, and 64 bits -/

def W8 : Nat := 8
def W16 : Nat := 16
def W32 : Nat := 32
def W64 : Nat := 64
def ptrofs_wordsize : Nat := if archi.ptr64 then W64 else W32

abbrev byte := word W8
abbrev int32 := word W32
abbrev int64 := word W64
abbrev ptrofs := word ptrofs_wordsize

theorem byte_wordsize_dvd_modulus : W8 ∣ modulus W8 := sorry
theorem int32_wordsize_dvd_modulus : W32 ∣ modulus W32 := sorry
theorem int64_wordsize_dvd_modulus : W64 ∣ modulus W64 := sorry

theorem ptrofs_wordsize_dvd_modulus :
  ptrofs_wordsize ∣ modulus ptrofs_wordsize := sorry

namespace int64

def is_power2 (x : int64) : Option int32 :=
  match word.is_power2 x with
  | some logn => some (word.repr (word.unsigned logn : Int))
  | none => none

lemma is_power2_rng (n logn : int64) : is_power2 n = some (word.repr (word.unsigned logn : Int)) → word.unsigned logn < 64 := sorry

theorem is_power2_range (n : int64) (logn : int32) : is_power2 n = some logn → word.ltu logn (word.repr 32) := sorry

lemma is_power2_correct (n : int64) (logn : int32) : is_power2 n = some logn →
  word.unsigned n = 2^word.unsigned logn := sorry

theorem mul_pow2 (x n : int64) (logn : int32) : is_power2 n = some logn →
  x * n = word.shl x (word.repr (word.unsigned logn : Int)) := sorry

theorem divu_pow2 (x n : int64) (logn : int32) : is_power2 n = some logn →
  word.divu x n = word.shru x (word.repr (word.unsigned logn : Int)) := sorry

/- Decomposing 64-bit ints as pairs of 32-bit ints -/

def loword (n : int64) : int32 := word.repr (word.unsigned n : Int)

def hiword (n : int64) : int32 := word.repr (word.unsigned (word.shru n (word.repr 32)) : Int)

def ofwords (hi lo : int32) : int64 := word.or (word.shl (word.repr (word.unsigned hi : Int)) (word.repr 32)) (word.repr (word.unsigned lo : Int))

lemma bits_loword (n : int64) (i : Nat) : i < 32 → word.test_bit (loword n) i = word.test_bit n i := sorry

lemma bits_hiword (n : int64) (i : Nat) : i < 32 → word.test_bit (hiword n) i = word.test_bit n (i + 32) := sorry

lemma bits_ofwords (hi lo : int32) (i : Nat) :
  word.test_bit (ofwords hi lo) i = if i < 32 then word.test_bit lo i else word.test_bit hi (i - 32) := sorry

lemma lo_ofwords (hi lo : int32) : loword (ofwords hi lo) = lo := sorry

lemma hi_ofwords (hi lo : int32) : hiword (ofwords hi lo) = hi := sorry

lemma ofwords_recompose (n : int64) : ofwords (hiword n) (loword n) = n := sorry

lemma ofwords_add (lo hi : int32) : ofwords hi lo = word.repr (word.unsigned hi * 2^32 + word.unsigned lo) := sorry

lemma ofwords_add' (lo hi : int32) : word.unsigned (ofwords hi lo) = word.unsigned hi * 2^32 + word.unsigned lo := sorry

lemma ofwords_add'' (lo hi : int32) : word.signed (ofwords hi lo) = word.signed hi * 2^32 + word.unsigned lo := sorry

/- Expressing 64-bit operations in terms of 32-bit operations -/

lemma decompose_bitwise_binop {f : ∀ {w}, word w → word w → word w} {f' : Bool → Bool → Bool} :
  (∀ {w} (x y : word w) (i : Nat), i < word.wordsize w → word.test_bit (f x y) i = f' (word.test_bit x i) (word.test_bit y i)) →
  ∀ xh xl yh yl, f (ofwords xh xl) (ofwords yh yl) = ofwords (f xh yh) (f xl yl) := sorry

lemma decompose_and : ∀ xh xl yh yl,
  word.and (ofwords xh xl) (ofwords yh yl) = ofwords (word.and xh yh) (word.and xl yl) := sorry

lemma decompose_or : ∀ xh xl yh yl,
  word.or (ofwords xh xl) (ofwords yh yl) = ofwords (word.or xh yh) (word.or xl yl) := sorry

lemma decompose_xor : ∀ xh xl yh yl,
  word.xor (ofwords xh xl) (ofwords yh yl) = ofwords (word.xor xh yh) (word.xor xl yl) := sorry

lemma decompose_not (xh xl : int32) : word.not (ofwords xh xl) = ofwords (word.not xh) (word.not xl) := sorry

lemma decompose_shl_1 (xh xl : int32) (y : int32) : word.unsigned y < 32 → word.shl (ofwords xh xl) (word.repr (word.unsigned y : Int)) =
  ofwords (word.or (word.shl xh (word.repr (word.unsigned y : Int))) (word.shru xl (word.repr (32 - word.unsigned y : Int)))) (word.shl xl (word.repr (word.unsigned y : Int))) := sorry

lemma decompose_shl_2 (xh xl : int32) (y : int32) : 32 ≤ word.unsigned y → word.unsigned y < 64 →
  word.shl (ofwords xh xl) (word.repr (word.unsigned y : Int)) = ofwords (word.shl xl (word.repr (word.unsigned y - 32 : Int))) 0 := sorry

lemma decompose_shru_1 (xh xl : int32) (y : int32) : word.unsigned y < 32 → word.shru (ofwords xh xl) (word.repr (word.unsigned y : Int)) =
  ofwords (word.shru xh (word.repr (word.unsigned y : Int))) (word.or (word.shru xl (word.repr (word.unsigned y : Int))) (word.shl xh (word.repr (32 - word.unsigned y : Int)))) := sorry

lemma decompose_shru_2 (xh xl : int32) (y : int32) : 32 ≤ word.unsigned y → word.unsigned y < 64 →
  word.shru (ofwords xh xl) (word.repr (word.unsigned y : Int)) = ofwords 0 (word.shru xh (word.repr (word.unsigned y - 32 : Int))) := sorry

lemma decompose_shr_1 (xh xl : int32) (y : int32) : word.unsigned y < 32 → word.shr (ofwords xh xl) (word.repr (word.unsigned y : Int)) =
  ofwords (word.shr xh (word.repr (word.unsigned y : Int))) (word.or (word.shru xl (word.repr (word.unsigned y : Int))) (word.shl xh (word.repr (32 - word.unsigned y : Int)))) := sorry

lemma decompose_shr_2 (xh xl : int32) (y : int32) : 32 ≤ word.unsigned y → word.unsigned y < 64 →
  word.shr (ofwords xh xl) (word.repr (word.unsigned y : Int)) = ofwords (word.shr xh (word.repr 31)) (word.shr xh (word.repr (word.unsigned y - 32 : Int))) := sorry

def add_carry {w : Nat} (x y : word w) (c : word w) : Bool := sorry
def sub_borrow {w : Nat} (x y : word w) (b : word w) : Bool := sorry
def mulhu {w : Nat} (x y : word w) : word w := sorry
def words_of_int (sz : Nat) (n : Nat) : List (word 8) := sorry

lemma decompose_add (xh xl yh yl : int32) : (ofwords xh xl) + (ofwords yh yl) =
  ofwords (xh + yh + (if (add_carry xl yl 0) then 1 else 0)) (xl + yl) := sorry

lemma decompose_sub (xh xl yh yl : int32) : (ofwords xh xl) - (ofwords yh yl) =
  ofwords (xh - yh - (if (sub_borrow xl yl 0) then 1 else 0)) (xl - yl) := sorry

lemma mul_mulhu (x y : int32) : (word.repr (word.unsigned x : Int) : int64) * (word.repr (word.unsigned y : Int) : int64) = ofwords (mulhu x y) (x * y) := sorry

lemma decompose_mul (xh xl yh yl : int32) : (ofwords xh xl) * (ofwords yh yl) =
  ofwords (mulhu xl yl + xl * yh + xh * yl) (xl * yl) := sorry

lemma decompose_ltu (xh xl yh yl : int32) :
  word.ltu (ofwords xh xl) (ofwords yh yl) ↔ if xh = yh then word.ltu xl yl else word.ltu xh yh := sorry

lemma decompose_leu (xh xl yh yl : int32) : ¬word.ltu (ofwords yh yl) (ofwords xh xl) ↔
  if xh = yh then ¬word.ltu yl xl else word.ltu xh yh := sorry

lemma decompose_lt (xh xl yh yl : int32) :
  (ofwords xh xl) < (ofwords yh yl) ↔ if xh = yh then xl < yl else xh < yh := sorry

lemma decompose_le (xh xl yh yl : int32) : (ofwords xh xl) ≤ (ofwords yh yl) ↔
  if xh = yh then xl ≤ yl else xh < yh := sorry

lemma bytes_of_int64 (i : int64) :
  (words_of_int 8 (word.unsigned i)) =
  words_of_int 4 (word.unsigned (loword i)) ++ words_of_int 4 (word.unsigned (hiword i)) := sorry

end int64

/- * Specialization to offsets in pointer values -/

namespace ptrofs

def to_int (x : ptrofs) : int32 := word.repr (word.unsigned x : Int)

def to_int64 (x : ptrofs) : int64 := word.repr (word.unsigned x : Int)

def of_int (x : int32) : ptrofs := word.repr (word.unsigned x : Int)

def of_intu := of_int

def of_ints (x : int32) : ptrofs := word.repr (word.signed x)

def of_int64 (x : int64) : ptrofs := word.repr (word.unsigned x : Int)

def of_int64u := of_int64

def of_int64s (x : int64) : ptrofs := word.repr (word.signed x)

end ptrofs

end integers
end Compcert
