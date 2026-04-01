import Compcert.flocq

namespace Compcert
namespace archi
namespace arm

def ptr64 : Bool := false

def big_endian : Bool := false

def align_int64 := 8
def align_float64 := 8

def splitlong := true

def default_pl_64 : Bool × floats.nan_pl 53 := (false, sorry)

def choose_nan_64 (s1: Bool) (pl1: floats.nan_pl 53) (s2: Bool) (pl2: floats.nan_pl 53) : Bool × floats.nan_pl 53 := (false, sorry)

end arm
end archi
end Compcert
