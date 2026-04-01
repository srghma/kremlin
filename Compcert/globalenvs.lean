import Compcert.ast
import Compcert.integers
import Compcert.values
import Compcert.memory

namespace Compcert
namespace globalenvs

open Compcert.ast Compcert.integers Compcert.values Compcert.memory

axiom genv (F V : Type) : Type
instance {F V} : Inhabited (genv F V) := ⟨sorry⟩

axiom find_symbol {F V} : genv F V → ident → Option ident
axiom find_funct {F V} : genv F V → val → Option (fundef F)
axiom find_funct_ptr {F V} : genv F V → ident → Option (fundef F)
axiom find_var_info {F V} : genv F V → ident → Option (globvar V)

axiom init_mem {F V} : program F V → Option mem

end globalenvs
end Compcert
