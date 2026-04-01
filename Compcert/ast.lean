import Compcert.lib
import Compcert.integers
import Compcert.floats
import Compcert.maps
import Compcert.errors

namespace Compcert
namespace ast

open Compcert
open Compcert.integers
open Compcert.floats
open Compcert.maps
open Compcert.errors

/- * Syntactic elements -/

/- Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [pos_num] of positive integers. -/

abbrev ident := pos_num

/- The intermediate languages are weakly typed, using the following types: -/

inductive typ : Type
| Tint                /- 32-bit integers or pointers -/
| Tfloat              /- 64-bit double-precision floats -/
| Tlong               /- 64-bit integers -/
| Tsingle             /- 32-bit single-precision floats -/
| Tany32              /- any 32-bit value -/
| Tany64              /- any 64-bit value, i.e. any value -/
deriving DecidableEq, Inhabited

def Tptr : typ := if archi.ptr64 then typ.Tlong else typ.Tint
open typ

def typesize : typ → Int
| Tint    => 4
| Tfloat  => 8
| Tlong   => 8
| Tsingle => 4
| Tany32  => 4
| Tany64  => 8

lemma typesize_pos (ty : typ) : typesize ty > 0 :=
by cases ty <;> (unfold typesize; try decide)

/- Subtyping relation -/
def subtype : typ → typ → Bool
| Tint,    Tany32 => true
| Tsingle, Tany32 => true
| Tany32,  Tany32 => true
| Tint,    Tany64 => true
| Tfloat,  Tany64 => true
| Tlong,   Tany64 => true
| Tsingle, Tany64 => true
| Tany32,  Tany64 => true
| Tany64,  Tany64 => true
| ty1, ty2 => ty1 == ty2

/- * Memory chunks -/

inductive memory_chunk : Type
| Mint8signed     /- 8-bit signed integer -/
| Mint8unsigned   /- 8-bit unsigned integer -/
| Mint16signed    /- 16-bit signed integer -/
| Mint16unsigned  /- 16-bit unsigned integer -/
| Mint32          /- 32-bit integer or pointer -/
| Mint64          /- 64-bit integer -/
| Mfloat32        /- 32-bit single-precision float -/
| Mfloat64        /- 64-bit double-precision float -/
| Many32          /- any 32-bit value -/
| Many64          /- any 64-bit value -/
deriving DecidableEq, Inhabited
open memory_chunk

def memory_chunk.type : memory_chunk → typ
| Mint8signed    => Tint
| Mint8unsigned  => Tint
| Mint16signed   => Tint
| Mint16unsigned => Tint
| Mint32         => Tint
| Mint64         => Tlong
| Mfloat32       => Tsingle
| Mfloat64       => Tfloat
| Many32         => Tany32
| Many64         => Tany64

/- * Function signatures -/

inductive calling_convention : Type
| mk (fp_as_first_arg : Bool) (no_return : Bool) : calling_convention
deriving DecidableEq, Inhabited

def cc_default : calling_convention := calling_convention.mk false false

structure signature : Type where
  sig_args : List typ
  sig_res  : Option typ
  sig_cc   : calling_convention
deriving DecidableEq, Inhabited

/- * External functions -/

inductive external_function : Type
| EF_external (name : ident) (sg : signature)
| EF_builtin (name : ident) (sg : signature)
| EF_runtime (name : ident) (sg : signature)
| EF_vload (chunk : memory_chunk)
| EF_vstore (chunk : memory_chunk)
| EF_malloc
| EF_free
| EF_memcpy (sz al : Nat)
| EF_annot (text : String) (targs : List typ)
| EF_annot_val (text : String) (targ : typ)
| EF_inline_asm (text : String) (sg : signature) (clobbers : List String)
| EF_debug (kind : pos_num) (text : ident) (targs : List typ)

instance : DecidableEq external_function := fun _ _ => sorry
instance : Inhabited external_function := ⟨external_function.EF_malloc⟩

def ef_sig : external_function → signature
| (external_function.EF_external _ sg)        => sg
| (external_function.EF_builtin _ sg)         => sg
| (external_function.EF_runtime _ sg)         => sg
| (external_function.EF_vload chunk)             => ⟨[Tptr], some chunk.type, cc_default⟩
| (external_function.EF_vstore chunk)            => ⟨[Tptr, chunk.type], none, cc_default⟩
| (external_function.EF_malloc)                  => ⟨[Tptr], some Tptr, cc_default⟩
| (external_function.EF_free)                    => ⟨[Tptr], none, cc_default⟩
| (external_function.EF_memcpy _ _)            => ⟨[Tptr, Tptr], none, cc_default⟩
| (external_function.EF_annot _ targs)        => ⟨targs, none, cc_default⟩
| (external_function.EF_annot_val _ targ)     => ⟨[Tptr], some targ, cc_default⟩
| (external_function.EF_inline_asm _ sg _) => sg
| (external_function.EF_debug _ _ targs)   => ⟨targs, none, cc_default⟩

/- * Function definitions -/

inductive fundef (F : Type) : Type
| Internal (f : F) : fundef F
| External (ef : external_function) : fundef F
deriving Inhabited

instance {F} [DecidableEq F] : DecidableEq (fundef F) := fun _ _ => sorry

def transf_fundef {A B} (transf : A → B) : fundef A → fundef B
| (fundef.Internal f)  => fundef.Internal (transf f)
| (fundef.External ef) => fundef.External ef

def transf_partial_fundef {A B} (transf_partial : A → res B) : fundef A → res (fundef B)
| (fundef.Internal f)  => do let f' ← transf_partial f; return fundef.Internal f'
| (fundef.External ef) => return fundef.External ef

/- * Global definitions -/

structure globvar (V : Type) : Type where
  gv_info     : V
  gv_readonly : Bool
  gv_volatile : Bool
deriving DecidableEq, Inhabited

def transf_globvar {V W} (f : V → W) (g : globvar V) : globvar W :=
{ gv_info := f g.gv_info, gv_readonly := g.gv_readonly, gv_volatile := g.gv_volatile }

inductive globdef (F V : Type) : Type
| Gfun (f : fundef F) : globdef F V
| Gvar (v : globvar V) : globdef F V
deriving Inhabited

instance {F V} [DecidableEq F] [DecidableEq V] : DecidableEq (globdef F V) := fun _ _ => sorry

/- * Programs -/

structure program (F V : Type) : Type where
  prog_defs   : List (ident × globdef F V)
  prog_public : List ident
  prog_main   : ident

instance : Inhabited (program F V) := ⟨sorry⟩

instance {F V} [DecidableEq F] [DecidableEq V] : DecidableEq (program F V) := fun _ _ => sorry

/- * Arguments and results to builtin functions -/

inductive builtin_arg (A : Type) : Type
| BA            (x : A)                                            : builtin_arg A
| BA_int        (n : int32)                                        : builtin_arg A
| BA_long       (n : int64)                                        : builtin_arg A
| BA_float      (f : float)                                        : builtin_arg A
| BA_single     (f : float32)                                      : builtin_arg A
| BA_loadstack  (chunk : memory_chunk) (ofs : ptrofs)              : builtin_arg A
| BA_addrstack  (ofs : ptrofs)                                     : builtin_arg A
| BA_loadglobal (chunk : memory_chunk) (id : ident) (ofs : ptrofs) : builtin_arg A
| BA_addrglobal (id : ident) (ofs : ptrofs)                        : builtin_arg A
| BA_splitlong  (hi lo : builtin_arg A)                            : builtin_arg A

instance : Inhabited (builtin_arg A) := ⟨sorry⟩

instance {A} [DecidableEq A] : DecidableEq (builtin_arg A) := fun _ _ => sorry

inductive builtin_res (A : Type) : Type
| BR           (x : A)               : builtin_res A
| BR_none                            : builtin_res A
| BR_splitlong (hi lo : builtin_res A) : builtin_res A
deriving Inhabited

instance {A} [DecidableEq A] : DecidableEq (builtin_res A) := fun _ _ => sorry

end ast
end Compcert
