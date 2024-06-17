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
		{(x', y') | x' y'. (x', y') \<in> set xs \<and> dist (x, y) (x', y') \<le> sqrt (8 * d\<^sup>2)})"

section "Proof and Analysis" 

(*
The strategy is first showing that the cost is bounded by some expression depending on d solely,
then analyse the bound of the expression in n. 
The expression: C \<le> 2 * |{(a, b) | dist a b \<le> sqrt (8 * d^2)}|, see lemma dist_of_neighbors
*)

thm dist_of_neighbors

lemma C_find_in_grids_eq_neigborhood_sz:
"C_find_in_grids xs d (x, y) = length (neighborhood xs d x y)"
	unfolding C_find_in_grids_def Let_def by simp

lemma finite_points: 
"finite {q | q. q \<in> set xs \<and> dist (x, y)q \<le> sqrt (8 * d\<^sup>2)}"
proof - 
	have "finite (set xs)" 
		"{q | q. q \<in> set xs \<and> dist (x, y) q \<le> sqrt (8 * d\<^sup>2)} \<subseteq> set xs"
	  by blast+
	then show ?thesis 
	using finite_subset[of _ "set xs"] by presburger
qed 

lemma neighborhood_sz_upper:
	assumes "d > 0" "distinct xs"
	shows "length (neighborhood xs d x y) \<le> card (neighbor_set xs d (x, y))"
proof -
	let ?S = "neighbor_set xs d (x, y)"
	have "q \<in> set (neighborhood xs d x y) \<Longrightarrow> q \<in> set xs \<and> dist (x, y) q \<le> sqrt (8 * d^2)" for q 
		using dist_of_neighbors[OF assms(1), of _ _ xs x y]  neighborhood_subset[of xs d x y]
		by (metis in_mono prod.collapse)
	then have A: "set (neighborhood xs d x y) \<subseteq> ?S" 
		by fast
	have "?S \<subseteq> set xs" 
		by fastforce
	then have "finite ?S" 
		using finite_subset by fast
	with A have "card (set (neighborhood xs d x y)) \<le> card ?S" 
		using card_mono[of ?S] by blast
	then show ?thesis 
		using distinct_card[of "neighborhood xs d x y"] neighborhood_distinct[OF assms(2)] 
		by auto
qed 
theorem traverse_grids_upper:
	assumes "d > 0" "distinct xs" 
	shows "C_traverse_grids xs d \<le> card (\<Union>{(neighbor_set xs d p) | p. p \<in> set xs}) + length xs "
proof -
	let ?f = "(\<lambda>p. card (neighbor_set xs d p))"
	have A: "inj_on (neighbor_set xs d) (set xs)" 
		sorry
	have B: "disjoint ((neighbor_set xs d) ` set xs)"
		sorry
	have C: "N \<in> ((neighbor_set xs d) ` set xs) \<Longrightarrow> finite N" for N
		using finite_points 
		sorry
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
		using sum.reindex[OF A,of card] by fastforce
	also have "... = card (\<Union> ((neighbor_set xs d) ` set xs))"
		using card_Union_disjoint[OF B C] by presburger
	also have "... = card (\<Union> {(neighbor_set xs d p) | p. p \<in> set xs})" 
		using D by argo
	finally have "sum_list (map (C_find_in_grids xs d) xs) \<le> card (\<Union> {(neighbor_set xs d p) | p. p \<in> set xs})"
		.
	moreover have "length (filter ((<) 0) (map (find_in_grids xs d) xs)) \<le> length xs" 
		by force
	ultimately show ?thesis
		unfolding C_traverse_grids_def Let_def
		by (auto simp add: add_le_mono) 
qed 

lemma "\<Union>{(neighbor_set xs d p) | p. p \<in> set xs} = {}"

thm sum.reindex
thm card_Union_disjoint
end