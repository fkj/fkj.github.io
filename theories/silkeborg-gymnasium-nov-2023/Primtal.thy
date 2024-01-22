theory
  Primtal
imports
  Main
  "HOL-Computational_Algebra.Primes"
begin

abbreviation \<open>primes \<equiv> {p :: nat. prime p}\<close>

theorem \<open>\<not> (finite primes)\<close>
proof
  assume \<open>finite primes\<close>
  then have \<open>\<exists>b. \<forall>x \<in> primes. x \<le> b\<close>
    using finite_nat_set_iff_bounded_le by blast
  then obtain b :: nat where \<open>\<forall>x. prime x \<longrightarrow> x \<le> b\<close>
    by auto

  moreover have \<open>\<forall>n. \<exists>p :: nat. prime p \<and> n < p \<and> p \<le> fact n + 1\<close>
  proof
    fix n
    have n1: \<open>fact n + 1 \<noteq> 1\<close>
      by (metis add.commute add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel fact_nonzero of_nat_eq_1_iff of_nat_fact semiring_1_class.of_nat_simps(2))
    from prime_factor_nat[OF n1] obtain p :: nat
      where \<open>prime p\<close> and \<open>p dvd fact n + 1\<close>
      by auto
    then have \<open>p \<le> fact n + 1\<close>
      by (intro dvd_imp_le, auto)
    have \<open>n < p\<close>
    proof (rule ccontr)
      assume \<open>\<not> n < p\<close>
      then have \<open>p \<le> n\<close> by simp
      from \<open>prime p\<close> have \<open>p \<ge> 1\<close>
        by (cases p, auto)
      with \<open>p \<le> n\<close> have \<open>p dvd fact n\<close>
        by (intro dvd_fact)
      with \<open>p dvd fact n + 1\<close> have \<open>p dvd fact n + 1 - fact n\<close>
        by (rule dvd_diff_nat)
      then have \<open>p dvd 1\<close> by simp
      then have \<open>p \<le> 1\<close> by auto
      moreover from \<open>prime p\<close> have \<open>p > 1\<close>
        using prime_nat_iff by blast
      ultimately show False by auto
    qed
    with \<open>prime p\<close> and \<open>p \<le> fact n + 1\<close>
    show \<open>\<exists>p :: nat. prime p \<and> n < p \<and> p \<le> fact n + 1\<close>
      by blast
  qed
  then have \<open>\<exists>p. prime p \<and> p > b\<close>
    by auto
  ultimately show False
    by auto
qed

end