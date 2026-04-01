import Compcert.flocq

/- Indeterminate architecture -/

namespace Compcert
namespace archi
open Compcert.flocq

def ptr64 : Bool := sorry

def big_endian : Bool := sorry

def align_int64 : Nat := sorry
def align_float64 : Nat := sorry

def splitlong : Bool := sorry

lemma splitlong_ptr32 : splitlong = true → ptr64 = false := sorry

def default_pl_64 : Bool × nan_pl 53 := sorry

def choose_binop_pl_64 (s1 : Bool) (pl1 : nan_pl 53) (s2 : Bool) (pl2 : nan_pl 53) : Bool := sorry

def default_pl_32 : Bool × nan_pl 24 := sorry

def choose_binop_pl_32 (s1 : Bool) (pl1 : nan_pl 24) (s2 : Bool) (pl2 : nan_pl 24) : Bool := sorry

def float_of_single_preserves_sNaN : Bool := sorry

end archi
end Compcert
