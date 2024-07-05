theory Closest_Pair_Cost
 	imports Closest_Pair_New
begin

section "Cost functions"

(*Any arithmetic computation is regarded as constant cost,
	what we are interested are 
	1. The cost of building grids, lists etc.
	2. The cost of comparisons while travering the grids and lists
	We use C for the number of comparisons and T for the actual running time including both.
	The analysis of C is presented, T may follow if necessary.
*)

definition C_brute_force_dist :: "(point \<times> point) list \<Rightarrow> nat" where 
"C_brute_force_dist xs = (if xs = [] then 1 else length (map (\<lambda>(p, q). dist p q) xs))"

fun C_build_pairs :: "point list \<Rightarrow> nat" where 
"C_build_pairs [] = 0" | 
"C_build_pairs [x] = 0" | 
"C_build_pairs (x # y # xs) = length (map (\<lambda>z. (x, z)) (y # xs)) + C_build_pairs (y # xs)"


definition C_find_in_grids :: "point list \<Rightarrow> real \<Rightarrow> point \<Rightarrow> nat" where 
"C_find_in_grids xs d = (\<lambda>(x, y). 
		let neighborhood = (neighborhood xs d x y) in
				(if neighborhood = [] then 0 
				else length (map (\<lambda>(p, q). dist p q) (map (\<lambda>z. ((x, y), z)) neighborhood))))"

definition C_traverse_grids :: "point list \<Rightarrow> real \<Rightarrow> nat" where 
"C_traverse_grids xs d = (let 
	result = filter (\<lambda>d. d > 0) (map (\<lambda>p. find_in_grids xs d p) xs);
	cost = sum_list (map (C_find_in_grids xs d) xs) in 
	if result = [] then cost else cost + length result)"

section "Randomized Implementation"

definition C_closest_pair :: "point list \<Rightarrow> nat pmf" where 
"C_closest_pair ps = do {
	d \<leftarrow> first_phase ps;
	return_pmf (1 + (C_traverse_grids ps d))
}"

abbreviation "neighbor_set xs d \<equiv> (\<lambda>(x, y). 
		{((x, y), (x', y')) | x' y'. (x', y') \<in> set xs \<and> dist (x, y) (x', y') < sqrt (8 * d\<^sup>2)})"

definition "close_point_count xs d \<equiv> card {(p, q) | p q. p \<in> set xs \<and> q \<in> set xs \<and> dist p q < d}"

section "Proof and Analysis" 

(*
The strategy is first showing that the cost is bounded by some expression depending on d solely,
then analyse the bound of the expression in n. 
The expression: C \<le> 2 * |{(a, b) | dist a b < sqrt (8 * d^2)}|, see lemma dist_of_neighbors
*)

thm dist_of_neighbors

lemma C_find_in_grids_eq_neigborhood_sz:
"C_find_in_grids xs d (x, y) = length (neighborhood xs d x y)"
	unfolding C_find_in_grids_def Let_def by simp

lemma finite_points: 
"finite {(p, q) | q. q \<in> set xs \<and> dist p q < sqrt (8 * d\<^sup>2)}"
proof - 
	have "finite (set xs)" 
		"{q | q. q \<in> set xs \<and> dist p q < sqrt (8 * d\<^sup>2)} \<subseteq> set xs"
	  by blast+
	then have "finite {q | q. q \<in> set xs \<and> dist p q < sqrt (8 * d\<^sup>2)}"
		by simp
	moreover have "Pair p ` {q | q. q \<in> set xs \<and> dist p q < sqrt (8 * d\<^sup>2)} 
		= {(p, q) | q. q \<in> set xs \<and> dist p q < sqrt (8 * d\<^sup>2)}"
		by blast
	ultimately show ?thesis 
		using finite_imageI[of "{q | q. q \<in> set xs \<and> dist p q < sqrt (8 * d\<^sup>2)}" "\<lambda>q. (p, q)"] 
		by argo
qed 

lemma neighborhood_sz_upper:
	assumes "d > 0" "distinct xs"
	shows "length (neighborhood xs d x y) \<le> card (neighbor_set xs d (x, y))"
proof -
	let ?S = "neighbor_set xs d (x, y)"
	have "q \<in> set (neighborhood xs d x y) \<Longrightarrow> q \<in> set xs \<and> dist (x, y) q < sqrt (8 * d^2)" for q 
		using dist_of_neighbors[OF assms(1), of _ _ xs x y]  neighborhood_subset[of xs d x y]
		by (metis in_mono prod.collapse)
	then have A: "Pair (x, y) ` set (neighborhood xs d x y) \<subseteq> ?S" 
		by fast
	have "?S \<subseteq> Pair (x, y) ` set xs" 
		by fastforce
	then have "finite ?S" 
		using finite_subset by fast
	with A have B: "card (Pair (x, y)` set (neighborhood xs d x y)) \<le> card ?S" 
		using card_mono[of ?S] by blast thm distinct_card
	have "distinct ys \<Longrightarrow> distinct (map (Pair (x, y)) ys)" for ys 
		by (induction ys) auto
	then have "distinct (map (Pair (x, y)) (neighborhood xs d x y))" 
		using neighborhood_distinct[OF assms(2), of d x y] 
		by blast
	moreover have "length (map (Pair (x, y)) (neighborhood xs d x y)) = length (neighborhood xs d x y)"
		by simp
	ultimately show ?thesis 
		using B distinct_card[of "(map (Pair (x, y)) (neighborhood xs d x y))"]
		by fastforce
qed  

thm inj_on_def

theorem traverse_grids_upper:
	assumes "d > 0" "distinct xs" 
	shows "C_traverse_grids xs d \<le> close_point_count xs (sqrt 8 * d) + length xs "
proof -
	let ?f = "(\<lambda>p. card (neighbor_set xs d p))"
	have A: "disjoint ((neighbor_set xs d) ` set xs)"
	proof -
		have "\<forall>a \<in> set xs. \<forall>b \<in> set xs. a \<noteq> b \<longrightarrow> neighbor_set xs d a \<inter> neighbor_set xs d b = {}"
			by fast
		then show ?thesis
			unfolding disjoint_def by blast
	qed 
	then have B: "inj_on (neighbor_set xs d) (set xs)" 
	proof -
		have "\<forall>a \<in> set xs. \<forall>b \<in> set xs. a \<noteq> b \<longrightarrow> neighbor_set xs d a \<inter> neighbor_set xs d b = {}"
			by fast
		moreover have "\<forall>a \<in> set xs. neighbor_set xs d a \<noteq> {}" 
			using assms(1) by force
		ultimately show ?thesis
			unfolding inj_on_def by force 
	qed
	have C: "N \<in> ((neighbor_set xs d) ` set xs) \<Longrightarrow> finite N" for N
		using finite_points by auto
	have D: "{(neighbor_set xs d p) | p. p \<in> set xs} = (neighbor_set xs d) ` set xs" 
		by blast
	have "\<And>p. p \<in> set xs \<Longrightarrow> C_find_in_grids xs d p \<le> ?f p"
		using neighborhood_sz_upper[OF assms] C_find_in_grids_eq_neigborhood_sz by force
	then have "sum_list (map (C_find_in_grids xs d) xs) \<le> sum_list (map ?f xs)"
		using sum_list_mono[of xs "C_find_in_grids xs d" ?f]
		by fastforce
	also have "... = sum ?f (set xs)"
		using monoid_add_class.sum_list_distinct_conv_sum_set[OF assms(2)] by fast
	also have "... = sum card ((neighbor_set xs d) ` set xs)" 
		using sum.reindex[OF B,of card] by fastforce
	also have "... = card (\<Union> ((neighbor_set xs d) ` set xs))"
		using card_Union_disjoint[OF A C] by presburger
	also have "... = card (\<Union> {(neighbor_set xs d p) | p. p \<in> set xs})" 
		using D by argo
	finally have "sum_list (map (C_find_in_grids xs d) xs) \<le> card (\<Union> {(neighbor_set xs d p) | p. p \<in> set xs})"
		.
	moreover have "length (filter ((<) 0) (map (find_in_grids xs d) xs)) \<le> length xs" 
		by force
	ultimately have "C_traverse_grids xs d \<le> card (\<Union>{(neighbor_set xs d p) | p. p \<in> set xs}) 
																						+ length xs"
		unfolding C_traverse_grids_def Let_def
		by (auto simp add: add_le_mono) 
	moreover have "\<Union>{(neighbor_set xs d p) | p. p \<in> set xs} 
		= {(p, q) | p q. p \<in> set xs \<and> q \<in> set xs \<and>  dist p q < sqrt 8 * d}" (is "?L = ?R")
	proof -
		have "sqrt (8 * d^2) = sqrt 8 * d" 
			using assms(1) by (simp add: real_sqrt_mult)
		then show ?thesis by auto
	qed 
	ultimately show ?thesis 
		unfolding close_point_count_def by argo
qed 

theorem traverse_grids_upper2:
assumes "d > 0" "distinct xs"
shows "C_traverse_grids xs d \<le> 100 * close_point_count xs d + length xs"
	sorry

section "Expectation"


lemma finite_replicate_pmf:
  assumes "finite (set_pmf p)"
  shows "finite (set_pmf (replicate_pmf n p))"
proof -
  have "(set_pmf (replicate_pmf n p)) = {xs. set xs \<subseteq> set_pmf p \<and> length xs = n}"
    unfolding set_replicate_pmf in_lists_conv_set by auto
  thus ?thesis using assms finite_lists_length_eq by auto
qed

lemma finite_map_pmf:
  assumes "finite (set_pmf p)"
  shows "finite (set_pmf (map_pmf f p))"
  unfolding map_pmf_def using assms by simp

lemma finite_first_phase:
  assumes "distinct ps"
  assumes "length ps \<ge> 2"
  shows "finite (set_pmf (first_phase ps))"
proof -
  have "build_pairs ps \<noteq> []"
  	using assms(2) by (induction ps rule: build_pairs.induct) auto
  hence "set_pmf (pmf_of_set (set (build_pairs ps))) = set (build_pairs ps)"
    by (intro set_pmf_of_set) auto
  hence "finite (set_pmf (pmf_of_set (set (build_pairs ps))))" by simp
  thus "finite (set_pmf (first_phase ps))"
    unfolding first_phase_def map_pmf_def[symmetric] 
    by (intro finite_replicate_pmf finite_map_pmf) simp
qed

lemma first_phase_pos:
  assumes "distinct ps"
  assumes "length ps \<ge> 2"
  shows "AE d in first_phase ps. d > 0"
proof -
  have a:"AE d in first_phase ps. d \<in> {min_dist ps..}"
    using first_phase_correct[OF assms] 
    by (intro  measure_pmf.AE_prob_1) (simp add: atLeast_def)
  show ?thesis using min_dist_pos[OF assms]
    by (intro eventually_mono[OF a]) simp
qed


definition A :: real where "A = undefined"  (* To be determined. *)
definition B :: real where "B = undefined"  (* To be determined. *)

lemma 
  assumes "distinct ps"
  assumes "length ps \<ge> 2"
  shows "measure_pmf.expectation (C_closest_pair ps) real \<le> A + B * length ps"
  (is "?LHS \<le> ?RHS")
proof -
  have "?LHS = measure_pmf.expectation (first_phase ps \<bind> (\<lambda>d. return_pmf (1+C_traverse_grids ps d))) real"
    unfolding C_closest_pair_def by simp
  also have "... = measure_pmf.expectation (map_pmf (\<lambda>d. 1 + C_traverse_grids ps d) (first_phase ps)) real"
    unfolding map_pmf_def by simp
  also have "... = measure_pmf.expectation (first_phase ps) (\<lambda>d. 1 + real (C_traverse_grids ps d))"
    by simp
  also have "... \<le> measure_pmf.expectation (first_phase ps) (\<lambda>d. 1 + length ps + 100 * close_point_count ps d)"
  proof (rule integral_mono_AE)
    show "integrable (measure_pmf (first_phase ps)) (\<lambda>x. real (1 + length ps +  100 * close_point_count ps x))"
      by (rule integrable_measure_pmf_finite[OF finite_first_phase[OF assms]])
    show "integrable (measure_pmf (first_phase ps)) (\<lambda>d. 1 + real (C_traverse_grids ps d))"
      by (rule integrable_measure_pmf_finite[OF finite_first_phase[OF assms]])
    show "AE x in measure_pmf (first_phase ps). 
      1 + real (C_traverse_grids ps x) \<le> real (1 + length ps + 100 * close_point_count ps x)"
    proof (rule eventually_mono[OF first_phase_pos[OF assms]])
      fix d :: real
      assume "d > 0"
      then show "1 + real (C_traverse_grids ps d) \<le> real (1 + length ps +  100 * close_point_count ps d)"
        using traverse_grids_upper2[OF _ assms(1)] by fastforce
    qed
  qed
  also have "... = measure_pmf.expectation (replicate_pmf (length ps) (pmf_of_set (set (build_pairs ps))))
									(\<lambda>xs. real (1 + length ps + 100 * close_point_count ps (brute_force_dist xs)))"
		unfolding first_phase_def map_pmf_def[symmetric] by simp
		
  show ?thesis sorry (* TODO *)
qed

lemma "measure_pmf.expectation 
	(replicate_pmf (length ps) (pmf_of_set (set (build_pairs ps)))) 
		(\<lambda>xs. close_point_count ps (brute_force_dist xs)) = length ps / 2"
	
	sorry

thm build_pairs.simps
thm close_point_count_def

lemma aux:
	assumes "length ps = n" "S \<subseteq> set (build_pairs ps)"
	shows "measure_pmf.expectation (replicate_pmf (length ps) (pmf_of_set S)) 
					(\<lambda>xs. close_point_count ps (brute_force_dist xs)) = card S / (length ps + 1)"
	sorry

thm integral_measure_pmf

find_theorems "replicate_pmf _ _"
find_theorems "measure_pmf.expectation (binomial_pmf _ _) _"

lemma expectation_binomial_pmf':
  fixes f :: "nat \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes p: "p \<in> {0..1}"
  shows   "measure_pmf.expectation (binomial_pmf n p) f =
             (\<Sum>k\<le>n. (real (n choose k) * p ^ k * (1 - p) ^ (n - k)) *\<^sub>R f k)"
  using p by (subst integral_measure_pmf[where A = "{..n}"])
             (auto simp: set_pmf_binomial_eq split: if_splits)
end