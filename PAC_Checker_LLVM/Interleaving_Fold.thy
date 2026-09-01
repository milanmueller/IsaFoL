theory Interleaving_Fold
  imports Main
begin

text \<open>This theory defines a generalization of the
  @{term foldl} function that allows traversal through two lists.
  In Isabelle_LLVM, using the Copying List implementation,
  this allows us to walk two lists simultaneously without
  destroying the original lists, as long as the inner functions
  keep their arguments intact.\<close>

text \<open>When traversing two lists, direction defines which list to
  recurse into\<close>
datatype direction = LEFT | RIGHT | BOTH | STOP

fun ifoldl :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> direction \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> direction)
  \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'a)
  \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'a\<close> where
  \<open>ifoldl _ _   _  _  acc [] []             = acc\<close>
| \<open>ifoldl _ _   f1 _  acc xs []             = foldl f1 acc xs\<close>
| \<open>ifoldl _ _   _  f2 acc [] ys             = foldl f2 acc ys\<close>
| \<open>ifoldl f dec f1 f2 acc (x # xs) (y # ys) = (
    case dec x y of
      STOP  \<Rightarrow> (f acc x y STOP)
    | LEFT  \<Rightarrow> ifoldl f dec f1 f2 (f acc x y LEFT)  xs (y # ys)
    | RIGHT \<Rightarrow> ifoldl f dec f1 f2 (f acc x y RIGHT) (x # xs) ys
    | BOTH  \<Rightarrow> ifoldl f dec f1 f2 (f acc x y BOTH)  xs ys
  )\<close>

end
