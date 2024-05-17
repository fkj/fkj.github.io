theory McCarthy imports Main begin

function M :: \<open>int \<Rightarrow> _\<close> where \<open>M n = (if n > 100 then n - 10 else M (M (n + 11)))\<close>
  by simp_all

termination
proof
  let ?R = \<open>measure (\<lambda>n. nat (101 - n))\<close>
  show \<open>wf ?R\<close> ..
  fix n :: int
  assume \<open>\<not> n > 100\<close>
  moreover from this show \<open>(n + 11, n) \<in> ?R\<close>
    by simp
  assume \<open>M_dom (n + 11)\<close>
  moreover have \<open>n - 10 \<le> M n\<close> if \<open>M_dom n\<close> for n
    using that by induct (force simp: M.psimps)
  ultimately show \<open>(M (n + 11), n) \<in> ?R\<close>
    by force
qed

theorem \<open>M n = (if n > 100 then n - 10 else 91)\<close>
  by (induct n rule: M.induct) simp

end
