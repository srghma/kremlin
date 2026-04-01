import Compcert.lib
import Mathlib.Data.Int.Bitwise
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Ring.Basic

/- * Parameterization by the word size, in bits. -/

namespace Compcert

namespace word
section
variable (n : Nat)

def wordsize : Nat := n

def modulus : Nat := 2^(wordsize n)
def half_modulus : Nat := 2^(wordsize n - 1)
def max_unsigned : Nat := modulus n - 1
def max_signed : Nat := half_modulus n - 1
def min_signed : Int := - (half_modulus n : Int)

theorem modulus_pos : modulus n > 0 := Nat.pow_pos (by decide)

theorem succ_max_unsigned : (max_unsigned n).succ = modulus n :=
  Nat.succ_pred_eq_of_pos (modulus_pos _)
end
end word

/- * Representation of machine integers -/

/- A machine integer (type [word]) is represented as an arbitrary-precision
  natural number (type [nat]) plus a proof that it is less than [modulus]. -/

def word (n : Nat) := Fin (word.modulus n)

namespace word

instance (w : Nat) : DecidableEq (word w) := inferInstanceAs (DecidableEq (Fin (word.modulus w)))

def repr {w : Nat} (x : Int) : word w :=
  ⟨(Compcert.int.nat_mod x (word.modulus w)), sorry⟩

def unsigned {w : Nat} (n : word w) : Nat := n.val

def signed {w : Nat} (n : word w) : Int :=
  let x := unsigned n
  if x < word.half_modulus w then (x : Int) else (x : Int) - (word.modulus w : Int)

/- Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. -/

def in_srange (w : Nat) (x : Int) : Bool := (word.min_signed w ≤ x) && (x < (word.half_modulus w : Int))
def in_urange (w : Nat) (x : Nat) : Bool := x < word.modulus w

def iwordsize (w : Nat) : word w := repr (w : Int)

instance {w : Nat} : Zero (word w) := ⟨repr 0⟩
instance {w : Nat} : One (word w) := ⟨repr 1⟩

def add {w : Nat} (x y : word w) : word w := repr ((unsigned x : Int) + (unsigned y : Int))
def mul {w : Nat} (x y : word w) : word w := repr ((unsigned x : Int) * (unsigned y : Int))
def neg {w : Nat} (x : word w) : word w := repr (-(unsigned x : Int))
def sub {w : Nat} (x y : word w) : word w := repr ((unsigned x : Int) - (unsigned y : Int))

instance {w : Nat} : Add (word w) := ⟨add⟩
instance {w : Nat} : Mul (word w) := ⟨mul⟩
instance {w : Nat} : Neg (word w) := ⟨neg⟩
instance {w : Nat} : Sub (word w) := ⟨sub⟩

/- * Arithmetic and logical operations over machine integers -/

def ltu {w : Nat} (x y : word w) : Prop := unsigned x < unsigned y
def leu {w : Nat} (x y : word w) : Prop := unsigned x ≤ unsigned y

instance (w : Nat) (x y : word w) : Decidable (ltu x y) :=
  inferInstanceAs (Decidable (unsigned x < unsigned y))
instance (w : Nat) (x y : word w) : Decidable (leu x y) :=
  inferInstanceAs (Decidable (unsigned x ≤ unsigned y))

instance {w : Nat} : LT (word w) := ⟨fun x y => signed x < signed y⟩
instance {w : Nat} : LE (word w) := ⟨fun x y => signed x ≤ signed y⟩

def divs {w : Nat} (x y : word w) : word w := repr (Compcert.int.quot (signed x) (signed y))
def mods {w : Nat} (x y : word w) : word w := repr (Compcert.int.rem  (signed x) (signed y))
instance {w : Nat} : Div (word w) := ⟨divs⟩
instance {w : Nat} : Mod (word w) := ⟨mods⟩

def divu {w : Nat} (x y : word w) : word w := repr (unsigned x / unsigned y : Nat)
def modu {w : Nat} (x y : word w) : word w := repr (unsigned x % unsigned y : Nat)

/- Bitwise boolean operations. -/

def and {w : Nat} (x y : word w) : word w := repr (Int.land (unsigned x) (unsigned y))
def or  {w : Nat} (x y : word w) : word w := repr (Int.lor  (unsigned x) (unsigned y))
def xor {w : Nat} (x y : word w) : word w := repr (Int.xor (unsigned x) (unsigned y))
def not {w : Nat} (x : word w) : word w := xor x (repr (-1 : Int))

def shl  {w : Nat} (x y : word w) : word w := repr (Int.shiftLeft (unsigned x) (unsigned y))
def shru {w : Nat} (x y : word w) : word w := repr (Nat.shiftRight (unsigned x) (unsigned y))
def shr  {w : Nat} (x y : word w) : word w := repr (Int.shiftRight (signed x) (unsigned y))

def shrx {w : Nat} (x y : word w) : word w := divs x (shl (repr 1) y)

def rol {w : Nat} (x y : word w) : word w :=
  let n := (unsigned y) % w
  or (shl x (repr (n : Int))) (shru x (repr (w - n : Int)))

def ror {w : Nat} (x y : word w) : word w :=
  let n := (unsigned y) % w
  or (shru x (repr (n : Int))) (shl x (repr (w - n : Int)))

def rolm {w : Nat} (x amount mask : word w) : word w := and (rol x amount) mask

/- * Rotations and shifts. -/

/- * Logical negation. -/

def is_true {w : Nat} (x : word w) : Prop := x ≠ 0
def is_false {w : Nat} (x : word w) : Prop := x = 0

def notbool {w : Nat} (x : word w) : word w :=
  if x = 0 then 1 else 0

/- * Bit-level operations. -/

def test_bit {w : Nat} (x : word w) (n : Nat) : Bool :=
  Nat.testBit (unsigned x) n

def set_bit {w : Nat} (x : word w) (n : Nat) (b : Bool) : word w :=
  if b
  then or x (shl 1 (repr (n : Int)))
  else and x (not (shl 1 (repr (n : Int))))

/- Recognition of powers of two. -/

def is_power2 {w : Nat} (x : word w) : Option (word w) :=
  let val := unsigned x
  if val = 0 then none
  else if (val &&& (val - 1)) = 0 then
    some (repr (val.log2 : Int))
  else none

/- Comparisons. -/

def cmp {w : Nat} : comparison → word w → word w → Bool
| comparison.Ceq, x, y => (decide (x = y))
| comparison.Cne, x, y => (decide (x ≠ y))
| comparison.Clt, x, y => (decide (x < y))
| comparison.Cle, x, y => (decide (x ≤ y))
| comparison.Cgt, x, y => (decide (y < x))
| comparison.Cge, x, y => (decide (y ≤ x))

def cmpu {w : Nat} : comparison → word w → word w → Bool
| comparison.Ceq, x, y => (decide (x = y))
| comparison.Cne, x, y => (decide (x ≠ y))
| comparison.Clt, x, y => (decide (ltu x y))
| comparison.Cle, x, y => (decide (leu x y))
| comparison.Cgt, x, y => (decide (ltu y x))
| comparison.Cge, x, y => (decide (leu y x))

def negate_comparison : comparison → comparison
| comparison.Ceq => comparison.Cne
| comparison.Cne => comparison.Ceq
| comparison.Clt => comparison.Cge
| comparison.Cle => comparison.Cgt
| comparison.Cgt => comparison.Cle
| comparison.Cge => comparison.Clt

def swap_comparison : comparison → comparison
| comparison.Ceq => comparison.Ceq
| comparison.Cne => comparison.Cne
| comparison.Clt => comparison.Cgt
| comparison.Cle => comparison.Cge
| comparison.Cgt => comparison.Clt
| comparison.Cge => comparison.Cle

/- Properties of machine integers. -/

/- Properties of [unsigned] and [signed]. -/

theorem unsigned_range {w : Nat} (x : word w) : unsigned x < word.modulus w := x.isLt

theorem unsigned_range_2 {w : Nat} (x : word w) : 0 ≤ unsigned x ∧ unsigned x ≤ word.max_unsigned w :=
  ⟨Nat.zero_le _, Nat.le_pred_of_lt (unsigned_range x)⟩

theorem signed_range {w : Nat} (x : word w) : word.min_signed w ≤ signed x ∧ signed x ≤ word.max_signed w := sorry

theorem repr_unsigned {w : Nat} (x : word w) : repr (unsigned x) = x := sorry

theorem unsigned_repr {w : Nat} (z : Int) : 0 ≤ z ∧ z ≤ word.max_unsigned w → unsigned (repr z : word w) = z.toNat := sorry

theorem signed_repr {w : Nat} (z : Int) : word.min_signed w ≤ z ∧ z ≤ word.max_signed w → signed (repr z : word w) = z := sorry

/- Addition, subtraction, negation. -/

theorem add_comm {w : Nat} (x y : word w) : add x y = add y x := sorry

theorem add_assoc {w : Nat} (x y z : word w) : add (add x y) z = add x (add y z) := sorry

@[simp] theorem add_zero {w : Nat} (x : word w) : add x 0 = x := sorry

@[simp] theorem zero_add {w : Nat} (x : word w) : add 0 x = x := sorry

theorem add_neg_zero {w : Nat} (x : word w) : add x (neg x) = 0 := sorry

theorem sub_add_opp {w : Nat} (x y : word w) : sub x y = add x (neg y) := sorry

@[simp] theorem sub_zero {w : Nat} (x : word w) : sub x 0 = x := sorry

theorem sub_add_l {w : Nat} (x y z : word w) : sub (add x y) z = add x (sub y z) := sorry

theorem sub_add_r {w : Nat} (x y z : word w) : sub x (add y z) = sub (sub x y) z := sorry

theorem sub_idem {w : Nat} (x : word w) : sub x x = 0 := sorry

theorem neg_add_distr {w : Nat} (x y : word w) : neg (add x y) = add (neg x) (neg y) := sorry

theorem neg_sub_distr {w : Nat} (x y : word w) : neg (sub x y) = sub y x := sorry

@[simp] theorem neg_neg {w : Nat} (x : word w) : neg (neg x) = x := sorry

/- Multiplication. -/

theorem mul_comm {w : Nat} (x y : word w) : mul x y = mul y x := sorry

theorem mul_assoc {w : Nat} (x y z : word w) : mul (mul x y) z = mul x (mul y z) := sorry

@[simp] theorem mul_one {w : Nat} (x : word w) : mul x 1 = x := sorry

@[simp] theorem one_mul {w : Nat} (x : word w) : mul 1 x = x := sorry

@[simp] theorem mul_zero {w : Nat} (x : word w) : mul x 0 = 0 := sorry

@[simp] theorem zero_mul {w : Nat} (x : word w) : mul 0 x = 0 := sorry

theorem mul_add_distr_l {w : Nat} (x y z : word w) : mul x (add y z) = add (mul x y) (mul x z) := sorry

theorem mul_add_distr_r {w : Nat} (x y z : word w) : mul (add x y) z = add (mul x z) (mul y z) := sorry

theorem mul_neg_l {w : Nat} (x y : word w) : mul (neg x) y = neg (mul x y) := sorry

theorem mul_neg_r {w : Nat} (x y : word w) : mul x (neg y) = neg (mul x y) := sorry

instance (w : Nat) : CommRing (word w) := sorry

/- Use the ring tactic for word w. -/

/- Bitwise operations. -/

theorem and_comm {w : Nat} (x y : word w) : and x y = and y x := sorry

theorem and_assoc {w : Nat} (x y z : word w) : and (and x y) z = and x (and y z) := sorry

@[simp] theorem and_self {w : Nat} (x : word w) : and x x = x := sorry

@[simp] theorem and_zero {w : Nat} (x : word w) : and x 0 = 0 := sorry

@[simp] theorem zero_and {w : Nat} (x : word w) : and 0 x = 0 := sorry

@[simp] theorem and_mone {w : Nat} (x : word w) : and x (repr (-1 : Int)) = x := sorry

theorem or_comm {w : Nat} (x y : word w) : or x y = or y x := sorry

theorem or_assoc {w : Nat} (x y z : word w) : or (or x y) z = or x (or y z) := sorry

@[simp] theorem zero_or {w : Nat} (x : word w) : or 0 x = x := sorry

@[simp] theorem or_mone {w : Nat} (x : word w) : or x (repr (-1 : Int)) = (repr (-1 : Int)) := sorry

@[simp] theorem or_self {w : Nat} (x : word w) : or x x = x := sorry

theorem xor_comm {w : Nat} (x y : word w) : xor x y = xor y x := sorry

theorem xor_assoc {w : Nat} (x y z : word w) : xor (xor x y) z = xor x (xor y z) := sorry

@[simp] theorem xor_zero {w : Nat} (x : word w) : xor x 0 = x := sorry

@[simp] theorem zero_xor {w : Nat} (x : word w) : xor 0 x = x := sorry

@[simp] theorem xor_self {w : Nat} (x : word w) : xor x x = 0 := sorry

theorem or_and_distr_l {w : Nat} (x y z : word w) : or x (and y z) = and (or x y) (or x z) := sorry

theorem or_and_distr_r {w : Nat} (x y z : word w) : or (and x y) z = and (or x z) (or y z) := sorry

theorem and_or_distr_l {w : Nat} (x y z : word w) : and x (or y z) = or (and x y) (and x z) := sorry

theorem and_or_distr_r {w : Nat} (x y z : word w) : and (or x y) z = or (and x z) (and y z) := sorry

theorem and_xor_distr_l {w : Nat} (x y z : word w) : and x (xor y z) = xor (and x y) (and x z) := sorry

theorem and_xor_distr_r {w : Nat} (x y z : word w) : and (xor x y) z = xor (and x z) (and y z) := sorry

theorem or_xor_distr_l {w : Nat} (x y z : word w) : or x (xor y z) = xor (or x y) (or x z) := sorry

theorem or_xor_distr_r {w : Nat} (x y z : word w) : or (xor x y) z = xor (or x z) (or y z) := sorry

theorem xor_and_distr_l {w : Nat} (x y z : word w) : xor x (and y z) = xor (and x y) (and x z) := sorry

theorem xor_and_distr_r {w : Nat} (x y z : word w) : xor (and x y) z = and (xor x z) (xor y z) := sorry

theorem xor_or_distr_l {w : Nat} (x y z : word w) : xor x (or y z) = or (xor x y) (xor x z) := sorry

theorem xor_or_distr_r {w : Nat} (x y z : word w) : xor (or x y) z = or (xor x z) (or y z) := sorry

/- Shifts. -/

theorem shl_zero {w : Nat} (x : word w) : shl x 0 = x := sorry

theorem shru_zero {w : Nat} (x : word w) : shru x 0 = x := sorry

theorem shr_zero {w : Nat} (x : word w) : shr x 0 = x := sorry

theorem shl_shl {w : Nat} (x y z : word w) : unsigned y + unsigned z < w → shl (shl x y) z = shl x (add y z) := sorry

theorem shru_shru {w : Nat} (x y z : word w) : unsigned y + unsigned z < w → shru (shru x y) z = shru x (add y z) := sorry

theorem shr_shr {w : Nat} (x y z : word w) : unsigned y + unsigned z < w → shr (shr x y) z = shr x (add y z) := sorry

theorem and_shl {w : Nat} (x y n : word w) : and (shl x n) (shl y n) = shl (and x y) n := sorry

theorem and_shru {w : Nat} (x y n : word w) : and (shru x n) (shru y n) = shru (and x y) n := sorry

theorem and_shr {w : Nat} (x y n : word w) : and (shr x n) (shr y n) = shr (and x y) n := sorry

theorem or_shl {w : Nat} (x y n : word w) : or (shl x n) (shl y n) = shl (or x y) n := sorry

theorem or_shru {w : Nat} (x y n : word w) : or (shru x n) (shru y n) = shru (or x y) n := sorry

theorem or_shr {w : Nat} (x y n : word w) : or (shr x n) (shr y n) = shr (or x y) n := sorry

theorem xor_shl {w : Nat} (x y n : word w) : xor (shl x n) (shl y n) = shl (xor x y) n := sorry

theorem xor_shru {w : Nat} (x y n : word w) : xor (shru x n) (shru y n) = shru (xor x y) n := sorry

theorem xor_shr {w : Nat} (x y n : word w) : xor (shr x n) (shr y n) = shr (xor x y) n := sorry

/- Rotations. -/

theorem rol_zero {w : Nat} (x : word w) : rol x 0 = x := sorry

theorem ror_zero {w : Nat} (x : word w) : ror x 0 = x := sorry

theorem rol_rol {w : Nat} (x y z : word w) : rol (rol x y) z = rol x (add y z) := sorry

theorem ror_ror {w : Nat} (x y z : word w) : ror (ror x y) z = ror x (add y z) := sorry

theorem rol_ror {w : Nat} (x y z : word w) : rol (ror x y) z = ror x (sub y z) := sorry

theorem ror_rol {w : Nat} (x y z : word w) : ror (rol x y) z = rol x (sub y z) := sorry

theorem and_rol {w : Nat} (x y n : word w) : rol (and x y) n = and (rol x n) (rol y n) := sorry

theorem and_ror {w : Nat} (x y n : word w) : ror (and x y) n = and (ror x n) (ror y n) := sorry

theorem or_rol {w : Nat} (x y n : word w) : rol (or x y) n = or (rol x n) (rol y n) := sorry

theorem or_ror {w : Nat} (x y n : word w) : ror (or x y) n = or (ror x n) (ror y n) := sorry

theorem xor_rol {w : Nat} (x y n : word w) : rol (xor x y) n = xor (rol x n) (rol y n) := sorry

theorem xor_ror {w : Nat} (x y n : word w) : ror (xor x y) n = xor (ror x n) (ror y n) := sorry

/- ** Properties of [is_power2]. -/

lemma is_power2_rng {w : Nat} (n logn : word w) : is_power2 n = some logn → unsigned logn < w := sorry

lemma is_power2_correct {w : Nat} (n logn : word w) : is_power2 n = some logn →
  unsigned n = 2^unsigned logn := sorry

theorem two_p_range {w : Nat} (n : Nat) : n < w → 2^n ≤ word.max_unsigned w := sorry

lemma is_power2_two_p {w : Nat} (n : Nat) (h : n < w) : is_power2 (repr (2^n : Int) : word w) = some (repr (n : Int) : word w) := sorry

/- ** Relation between bitwise operations and multiplications / divisions by powers of 2 -/

/- Left shifts and multiplications by powers of 2. -/

lemma shl_mul_two_p {w : Nat} (x y : word w) : shl x y = mul x (repr ((2 ^ unsigned y : Nat) : Int)) := sorry

theorem shl_mul {w : Nat} (x y : word w) : shl x y = mul x (shl 1 y) := sorry

theorem mul_pow2 {w : Nat} (x n logn : word w) : is_power2 n = some logn → mul x n = shl x logn := sorry

/- Unsigned right shifts and unsigned divisions by powers of 2. -/

lemma shru_div_two_p {w : Nat} (x y : word w) : shru x y = divu x (repr ((2 ^ unsigned y : Nat) : Int)) := sorry

theorem divu_pow2 {w : Nat} (x n logn : word w) : is_power2 n = some logn → divu x n = shru x logn := sorry

/- Signed right shifts and signed divisions by powers of 2. -/

lemma shr_div_two_p {w : Nat} (x y : word w) : shr x y = divs x (repr ((2 ^ unsigned y : Nat) : Int)) := sorry

theorem divs_pow2 {w : Nat} (x n logn : word w) : is_power2 n = some logn → divs x n = shrx x logn := sorry

/- Modulo and bitwise and. -/

theorem modu_and {w : Nat} (x n logn : word w) : is_power2 n = some logn → modu x n = and x (sub n (repr 1)) := sorry

/- General properties of [test_bit]. -/

theorem test_bit_repr {w : Nat} (z : Int) (n : Nat) : n < w → test_bit (repr z : word w) n = Nat.testBit z.toNat n := sorry

theorem test_bit_and {w : Nat} (x y : word w) (n : Nat) : n < w → test_bit (and x y) n = (test_bit x n && test_bit y n) := sorry

theorem test_bit_or {w : Nat} (x y : word w) (n : Nat) : n < w → test_bit (or x y) n = (test_bit x n || test_bit y n) := sorry

theorem test_bit_xor {w : Nat} (x y : word w) (n : Nat) : n < w → test_bit (xor x y) n = (test_bit x n != test_bit y n) := sorry

theorem test_bit_not {w : Nat} (x : word w) (n : Nat) : n < w → test_bit (not x) n = ! (test_bit x n) := sorry

/- Conversions between signed and unsigned integers. -/

theorem unsigned_signed {w : Nat} (x : word w) : repr (signed x) = x := sorry

theorem signed_unsigned {w : Nat} (x : word w) : signed (repr (unsigned x) : word w) = signed x := sorry

/- Comparison properties. -/

theorem negate_cmp {w : Nat} (c : comparison) (x y : word w) : cmp (negate_comparison c) x y = !(cmp c x y) := sorry

theorem swap_cmp {w : Nat} (c : comparison) (x y : word w) : cmp (swap_comparison c) x y = cmp c y x := sorry

theorem swap_cmpu {w : Nat} (c : comparison) (x y : word w) : cmpu (swap_comparison c) x y = cmpu c y x := sorry

lemma translate_ltu {w : Nat} (x y d : word w) :
  unsigned x + unsigned d ≤ word.max_unsigned w →
  unsigned y + unsigned d ≤ word.max_unsigned w →
  ltu x y ↔ ltu (add x d) (add y d) := sorry

theorem translate_cmpu {w : Nat} (c : comparison) (x y d : word w) :
  unsigned x + unsigned d ≤ word.max_unsigned w →
  unsigned y + unsigned d ≤ word.max_unsigned w →
  cmpu c (add x d) (add y d) = cmpu c x y := sorry

lemma translate_lt {w : Nat} (x y d : word w) :
  (in_srange w (signed x + signed d)) →
  (in_srange w (signed y + signed d)) →
  x < y ↔ (add x d) < (add y d) := sorry

theorem translate_cmp {w : Nat} (c : comparison) (x y d : word w) :
  (in_srange w (signed x + signed d)) →
  (in_srange w (signed y + signed d)) →
  cmp c (add x d) (add y d) = cmp c x y := sorry

theorem notbool_isfalse_istrue {w : Nat} (x : word w) : is_false x → is_true (notbool x) := sorry

theorem notbool_istrue_isfalse {w : Nat} (x : word w) : is_true x → is_false (notbool x) := sorry

theorem ltu_range_test {w : Nat} (x y : word w) : ltu x y → unsigned y ≤ word.max_signed w →
  0 ≤ signed x ∧ signed x < (unsigned y : Int) := sorry

lemma signed_eq {w : Nat} {x y : word w} : x = y ↔ signed x = signed y := sorry

lemma unsigned_eq {w : Nat} {x y : word w} : x = y ↔ unsigned x = unsigned y := sorry

lemma leu_ifalse_ltu_or_eq {w : Nat} (x y : word w) : leu x y ↔ ltu x y ∨ x = y := sorry

lemma le_ifalse_lt_or_eq {w : Nat} (x y : word w) : x ≤ y ↔ x < y ∨ x = y := sorry

/- Non-overlapping test -/

def no_overlap {w : Nat} (ofs1 : word w) (sz1 : Nat) (ofs2 : word w) (sz2 : Nat) : Bool :=
  let x1 := unsigned ofs1
  let x2 := unsigned ofs2
  (x1 + sz1 < word.modulus w) && (x2 + sz2 < word.modulus w) && ((x1 + sz1 ≤ x2) || (x2 + sz2 ≤ x1))

lemma no_overlap_sound {w : Nat} (ofs1 : word w) (sz1 : Nat) (ofs2 : word w) (sz2 : Nat) (base : word w) :
  sz1 > 0 → sz2 > 0 → (no_overlap ofs1 sz1 ofs2 sz2) →
  unsigned (add base ofs1) + sz1 ≤ unsigned (add base ofs2)
  ∨ unsigned (add base ofs2) + sz2 ≤ unsigned (add base ofs1) := sorry

/- Size of integers, in bits. -/

def size {w : Nat} (x : word w) : Nat := (unsigned x).size

theorem size_zero {w : Nat} : size (0 : word w) = 0 := sorry

theorem test_bit_size {w : Nat} (x : word w) : unsigned x > 0 → test_bit x (size x - 1) = true := sorry

theorem test_bit_size_lt {w : Nat} (x : word w) (i : Nat) : test_bit x i → i < size x := sorry

theorem size_le_wordsize {w : Nat} (x : word w) : size x ≤ w := sorry

theorem lt_pow_size {w : Nat} (x : word w) : unsigned x < 2^size x := sorry

theorem wordsize_dvd_modulus {w : Nat} (n : Nat) : w = 2^n → w ∣ word.modulus w := sorry

def scoe {w w' : Nat} (x : word w) : word w' := repr (signed x)
def ucoe {w w' : Nat} (x : word w) (w' : Nat) : word w' := repr (unsigned x : Int)

end word

structure uword (w : Nat) where
  toWord : word w

namespace uword
open word

instance uword_decEq {w : Nat} : DecidableEq (uword w) :=
  fun ⟨x⟩ ⟨y⟩ => match decEq x y with
    | isTrue h => isTrue (congrArg uword.mk h)
    | isFalse h => isFalse (fun h' => h (by injection h'))

def unsigned {w : Nat} (x : uword w) : Nat := word.unsigned x.toWord

instance {w : Nat} : Coe (uword w) (word w) := ⟨fun x => x.toWord⟩
instance {w : Nat} : Coe (word w) (uword w) := ⟨fun x => ⟨x⟩⟩

instance uword_zero {w : Nat} : Zero (uword w) := ⟨⟨0⟩⟩
instance uword_one {w : Nat} : One (uword w) := ⟨⟨1⟩⟩

instance uword_lt {w : Nat} : LT (uword w) := ⟨fun x y => ltu x.toWord y.toWord⟩
instance uword_le {w : Nat} : LE (uword w) := ⟨fun x y => leu x.toWord y.toWord⟩

instance uword_neg {w : Nat} : Neg (uword w) := ⟨fun x => ⟨neg x.toWord⟩⟩
instance uword_add {w : Nat} : Add (uword w) := ⟨fun x y => ⟨add x.toWord y.toWord⟩⟩
instance uword_mul {w : Nat} : Mul (uword w) := ⟨fun x y => ⟨mul x.toWord y.toWord⟩⟩

instance uword_div {w : Nat} : Div (uword w) := ⟨fun x y => ⟨divu x.toWord y.toWord⟩⟩
instance uword_mod {w : Nat} : Mod (uword w) := ⟨fun x y => ⟨modu x.toWord y.toWord⟩⟩

theorem zero_le {w : Nat} (x : uword w) : (0 : uword w) ≤ x :=
  show word.unsigned (0 : word w) ≤ word.unsigned x.toWord by sorry

end uword

end Compcert
