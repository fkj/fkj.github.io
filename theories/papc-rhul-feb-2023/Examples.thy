theory Examples
  imports
    Complex_Main
begin

section \<open>Main example\<close>
text \<open>Write a function that removes the first occurrence of a given element from a given list.\<close>
(*

datatype 'a list2 =
  Nil
| Cons 'a \<open>'a list2\<close>

datatype nat2 =
  Zero
  | Succ nat2

fun length where
  \<open>length Nil = Zero\<close>
| \<open>length (Cons x xs) = Succ (length xs)\<close>

fun less where
  \<open>less _ Zero = False\<close>
| \<open>less Zero _ = True\<close>
| \<open>less (Succ n) (Succ m) = less n m\<close>

fun set where
  \<open>set Nil = {}\<close>
| \<open>set (Cons x xs) = {x} \<union> set xs\<close>
*)
subsection \<open>Implementation\<close>
(*
fun remove1 where
  \<open>remove1 _ Nil = Nil\<close>
| \<open>remove1 y (Cons x xs) = (if x = y then xs else remove1 y xs)\<close>
*)
fun remove1 where
  \<open>remove1 _ Nil = Nil\<close>
| \<open>remove1 y (Cons x xs) = (if x = y then xs else Cons x (remove1 y xs))\<close>

subsection \<open>Specification\<close>

lemma \<open>y \<in> set xs \<Longrightarrow> less (length (remove1 y xs)) (length xs)\<close>
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases \<open>x = y\<close>)
    case True
    then have \<open>remove1 y (Cons x xs) = xs\<close>
      using Cons by simp
    then have \<open>length (remove1 y (Cons x xs)) = length xs\<close>
      by simp
    moreover have \<open>less (length xs) (length (Cons x xs))\<close>
      by (induction xs) auto
    ultimately show ?thesis
      by simp
  next
    case False
    then have \<open>y \<in> set xs\<close>
      using Cons by simp
    then have \<open>less (length (remove1 y xs)) (length xs)\<close>
      using Cons by simp
    then show ?thesis
      using False by simp
  qed
qed

lemma \<open>x \<noteq> y \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set (remove1 y xs)\<close>
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case by auto
qed

lemma \<open>y \<notin> set xs \<Longrightarrow> length xs = length (remove1 y xs)\<close>
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case by auto
qed

subsection \<open>Evaluation\<close>
value \<open>remove1 ''a'' (Cons ''a'' (Cons ''b'' (Cons ''a'' Nil)))\<close>

subsection \<open>Automation\<close>

lemma \<open>y \<in> set xs \<Longrightarrow> less (length (remove1 y xs)) (length xs)\<close>
  by (induction xs) auto

lemma \<open>x \<noteq> y \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set (remove1 y xs)\<close>
  by (induction xs) auto

lemma \<open>y \<notin> set xs \<Longrightarrow> length xs = length (remove1 y xs)\<close>
  by (induction xs) auto

subsection \<open>Sledgehammer\<close>

lemma \<open>xs @ ys = ys @ xs \<Longrightarrow> length xs = length ys \<Longrightarrow> xs = ys\<close>
  using append_eq_append_conv by blast

subsection \<open>Code export\<close>

export_code remove1 in Haskell

section \<open>Classical\<close>
subsection \<open>LEM\<close>

lemma \<open>p \<or> \<not> p\<close>
  by simp

subsection \<open>Proof by contradiction\<close>

lemma \<open>\<exists>x. drunk x \<longrightarrow> (\<forall>x. drunk x)\<close>
proof (cases \<open>\<forall>x. drunk x\<close>)
  case True
  then have \<open>drunk a \<longrightarrow> (\<forall>x. drunk x)\<close> for a by (rule impI)
  then show ?thesis by (rule exI)
next
  case False
  then have \<open>\<exists>x. \<not> drunk x\<close> by simp
  then obtain a where \<open>\<not> drunk a\<close> by (rule exE)
  have \<open>drunk a \<longrightarrow> (\<forall>x. drunk x)\<close>
  proof
    assume \<open>drunk a\<close>
    with \<open>\<not> drunk a\<close> show \<open>\<forall>x. drunk x\<close> by contradiction
  qed
  then show ?thesis by (rule exI)
qed

lemma \<open>\<exists>x. drunk x \<longrightarrow> (\<forall>x. drunk x)\<close>
  by blast

section \<open>Working with infinite sets\<close>

definition \<open>positive_reals \<equiv> {x | x. 0 < x} :: real set\<close>

section \<open>Axiom of choice (Hilbert epsilon)\<close>
definition \<open>smallest_positive_real \<equiv> Inf {x | x. 0 < x} :: real\<close>

section \<open>Coinduction and corecursion\<close>

codatatype (sset: 'a) Stream = SCons (shd: 'a) (stl: \<open>'a Stream\<close>)
  for map: smap

primcorec siterate :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream\<close> where
  \<open>siterate f a = SCons a (siterate f (f a))\<close>

lemma \<open>smap f (siterate f x) = siterate f (f x)\<close>
proof (coinduction arbitrary: x)
  case Eq_Stream
  then show ?case
    by (metis Stream.map_sel(1) Stream.map_sel(2) siterate.simps(1) siterate.simps(2))
qed 

primrec stake :: \<open>nat \<Rightarrow> 'a Stream \<Rightarrow> 'a list\<close> where
  \<open>stake 0 s = []\<close>
| \<open>stake (Suc n) s = shd s # stake n (stl s)\<close>

section \<open>Termination proofs\<close>

function sum :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sum i N = (if i > N then 0 else i + sum (Suc i) N)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(i,N). N + 1 - i)\<close>) auto

fun sum' where \<open>sum' n = sum 0 n\<close>

value \<open>sum' 10\<close>

end