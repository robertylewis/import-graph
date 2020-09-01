import meta.rb_map
import meta.expr 
import system.io 
import data.list.sort
import data.real.basic 
import all

/-!

Usage:

```

leanproject get robertylewis/import-graph
cd import-graph
lean --run src/gen_graph.lean

```

-/

@[inline]
meta def expr.get_constants (e : expr) : name_set :=
e.fold mk_name_set $ λ e' _ s, match e' with 
| expr.const nm _ := s.insert nm
| _ := s 
end 

@[inline]
meta def declaration.get_constants : declaration → name_set 
| (declaration.ax nm _ tp) := tp.get_constants
| (declaration.cnst nm _ tp is_meta) := tp.get_constants
| (declaration.thm nm _ tp bd) := tp.get_constants.union bd.get.get_constants
| (declaration.defn nm _ tp bd _ is_meta) := tp.get_constants.union bd.get_constants

open io io.fs tactic

meta instance coe_tactic_to_io {α} : has_coe (tactic α) (io α) :=
⟨run_tactic⟩

def fn := "graph.dot"

/-- hack to avoid memory error -/
meta def list.itersplit {α} : list α → ℕ → list (list α)
| l 0 := [l]
| l 1 := let (l1, l2) := l.split in [l1, l2]
| l (k+2) := let (l1, l2) := l.split in list.itersplit l1 (k+1) ++ list.itersplit l2 (k+1)

meta def main : io unit := do
h ← mk_file_handle fn mode.write,
e ← get_env,
let s := list.join $ e.fold [] $ λ d s, 
  let deps := d.get_constants in 
  deps.to_list.map (λ n, (d.to_name.to_string, n.to_string))::s,
let s := s.map (λ ⟨lhs, rhs⟩, ("\n\"" ++ lhs ++ "\" -> \"" ++ rhs ++ "\"")),
let s := s.itersplit 10,
s.mmap' $ λ s', s'.mmap' $  put_str h
