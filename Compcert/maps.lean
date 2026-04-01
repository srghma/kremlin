import Compcert.lib

namespace Compcert
namespace maps

inductive PTree (A : Type) : Type
| leaf : PTree A
| node : PTree A → Option A → PTree A → PTree A

namespace PTree

instance {A} : EmptyCollection (PTree A) := ⟨leaf⟩

def get {A} (i : Compcert.pos_num) (t : PTree A) : Option A :=
  match t, i with
  | leaf, _ => none
  | node _ o _, Compcert.pos_num.one => o
  | node l _ _, Compcert.pos_num.bit0 i' => get i' l
  | node _ _ r, Compcert.pos_num.bit1 i' => get i' r

def set {A} (i : Compcert.pos_num) (v : A) (t : PTree A) : PTree A :=
  match t, i with
  | leaf, Compcert.pos_num.one => node leaf (some v) leaf
  | leaf, Compcert.pos_num.bit0 i' => node (set i' v leaf) none leaf
  | leaf, Compcert.pos_num.bit1 i' => node leaf none (set i' v leaf)
  | node l _ r, Compcert.pos_num.one => node l (some v) r
  | node l o r, Compcert.pos_num.bit0 i' => node (set i' v l) o r
  | node l o r, Compcert.pos_num.bit1 i' => node l o (set i' v r)

def remove {A} (i : Compcert.pos_num) (t : PTree A) : PTree A :=
  match t, i with
  | leaf, _ => leaf
  | node l _ r, Compcert.pos_num.one => node l none r
  | node l o r, Compcert.pos_num.bit0 i' => node (remove i' l) o r
  | node l o r, Compcert.pos_num.bit1 i' => node l o (remove i' r)

def map {A B} (f : Compcert.pos_num → A → B) (t : PTree A) : PTree B :=
  let rec map' (i : Compcert.pos_num) (t : PTree A) : PTree B :=
    match t with
    | leaf => leaf
    | node l o r =>
        node (map' (Compcert.pos_num.bit0 i) l)
             (o.map (f i))
             (map' (Compcert.pos_num.bit1 i) r)
  map' Compcert.pos_num.one t

end PTree

end maps
end Compcert
