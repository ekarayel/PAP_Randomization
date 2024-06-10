theory Closest_Pair_New
	  imports "HOL-Probability.Probability_Mass_Function" 
begin

section "definitions"

type_synonym point = "real * real"

fun dist :: "point => point => real" where 
"dist (x1, y1) (x2, y2) = sqrt ((x1 - x2)^2 + (y1 - y2)^2)"


definition "min_dist_point p xs \<equiv> Min {dist p q | q. q \<in> set xs \<and> p \<noteq> q}"
definition "min_dist xs \<equiv> Min {min_dist_point p xs | p. p \<in> set xs}"

definition brute_force_dist :: "(point \<times> point) list \<Rightarrow> real" where 
"brute_force_dist xs = (if xs = [] then -1 else min_list (map (\<lambda>(p, q). dist p q) xs))"

fun build_pairs :: "point list \<Rightarrow> (point \<times> point) list" where 
"build_pairs [] = []" | 
"build_pairs [x] = []" | 
"build_pairs (x # y # xs) = (map (\<lambda>z. (x, z)) (y # xs)) @ build_pairs (y # xs)"

definition build_grid :: "point list \<Rightarrow> real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> point list" where 
"build_grid xs d a b = filter (\<lambda>(x, y). \<lfloor>x/d\<rfloor> = a \<and> \<lfloor>y/d\<rfloor> = b) xs"

definition neighbors_of_point :: "point list \<Rightarrow> real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> point list" where 
"neighbors_of_point xs d a b = 
	build_grid xs d a b @ build_grid xs d (a - 1) b @ build_grid xs d (a + 1) b @
	build_grid xs d a (b - 1) @ build_grid xs d (a - 1) (b - 1) @ build_grid xs d (a + 1) (b - 1) @
	build_grid xs d a (b + 1) @ build_grid xs d (a - 1) (b + 1) @ build_grid xs d (a + 1) (b + 1)
 "

definition "neighborhood xs d x y = filter (\<lambda>(x', y'). x = x' \<longrightarrow> y \<noteq> y') (neighbors_of_point xs d \<lfloor>x/d\<rfloor> \<lfloor>y/d\<rfloor>)"

definition find_in_grids :: "point list \<Rightarrow> real \<Rightarrow> point \<Rightarrow> real" where 
"find_in_grids xs d = (\<lambda>(x, y). 
		let neighborhood = (neighborhood xs d x y) in
				(if neighborhood = [] then 0 
				else min_list (map (\<lambda>(p, q). dist p q) (map (\<lambda>z. ((x, y), z)) neighborhood))))"

definition traverse_grids :: "point list \<Rightarrow> real \<Rightarrow> real" where 
"traverse_grids xs d = (let 
	result = filter (\<lambda>d. d > 0) (map (\<lambda>p. find_in_grids xs d p) xs) in 
	if result = [] then d else min_list result)"

section "Auxiliary Lemmas"

subsection Basics

lemma dist_symm: "dist p q = dist q p" 
  by (metis dist.simps surj_pair power2_commute)

lemma dist_nonneg: "dist p q \<ge> 0"
	by (metis dist.simps linorder_not_le not_sum_power2_lt_zero real_sqrt_ge_0_iff split_pairs)

lemma dist_pos: "p \<noteq> q \<Longrightarrow> dist p q > 0" 
proof-
	obtain x1 y1 x2 y2 where A: "p = (x1, y1)" "q = (x2, y2)"
		by force 
	moreover assume "p \<noteq> q"
	ultimately have "x1 \<noteq> x2 \<or> y1 \<noteq> y2" 
		by blast
	then have "(x1 - x2)^2 + (y1 - y2)^2 > 0" 
		by (simp add: sum_power2_gt_zero_iff)
	then show "dist p q > 0"
		using A by simp
qed 

lemma length_two_exists:
"distinct xs \<Longrightarrow> length xs \<ge> 2 \<Longrightarrow> p \<in> set xs \<Longrightarrow> set xs - {p} \<noteq> {}"
	apply (induction xs) apply auto 
	using subset_singletonD by fastforce

lemma min_dist_exists:
	assumes "xs \<noteq> []"
	shows "\<exists>p \<in> set xs. min_dist xs = min_dist_point p xs"
proof-
	from assms have "finite (set xs)" "set xs \<noteq> {}" 
		by auto
	then have "finite ({min_dist_point p xs |p. p \<in> set xs})" 
								"{min_dist_point p xs |p. p \<in> set xs} \<noteq> {}" 
		using finite_imageI[of "set xs" "\<lambda>p. min_dist_point p xs"]
		by (metis Setcompr_eq_image, metis Setcompr_eq_image image_is_empty)
	then show ?thesis
		unfolding min_dist_def 
		using Min_in by blast
qed 

lemma min_dist_point_exists:
	assumes "set xs - {p} \<noteq> {}"
	shows "\<exists>q \<in> set xs - {p}.  min_dist_point p xs = dist p q"
proof -
	from assms have "finite (set xs - {p})" 
		by auto
	with assms have "finite ({dist p q |q. q \<in> set xs - {p}})" 
								"{dist p q |q. q \<in> set xs - {p}} \<noteq> {}" 
		using finite_imageI[of "set xs - {p}" "\<lambda>q. dist p q"]
		by (metis Setcompr_eq_image, metis Setcompr_eq_image image_is_empty)
	then have "finite ({dist p q |q. q \<in> set xs \<and> q \<noteq> p})" 
				"{dist p q |q. q \<in> set xs \<and> q \<noteq> p} \<noteq> {}" 
		by fastforce+
	moreover have "q \<noteq> p = (p \<noteq> q)" for q
		by blast
	ultimately have  "finite ({dist p q |q. q \<in> set xs \<and> p \<noteq> q})" 
				"{dist p q |q. q \<in> set xs \<and> p \<noteq> q} \<noteq> {}"
		by force+
	then show ?thesis
		unfolding min_dist_point_def 
		using Min_in by fast
qed

lemma min_dist_le:
	fixes q
	assumes "q \<in> set xs"
	shows "min_dist xs \<le> min_dist_point q xs"
proof-
	from assms have "finite (set xs)" 
		by auto
	then have	"finite ({min_dist_point p xs |p. p \<in> set xs})" 
		using finite_imageI[of "set xs" "\<lambda>p. min_dist_point p xs"]
		by (metis Setcompr_eq_image)
	moreover have "min_dist_point q xs \<in> {min_dist_point p xs |p. p \<in> set xs}"
		using assms by fastforce
	ultimately show ?thesis
		unfolding min_dist_def 
		using Min_le by blast
qed 

lemma min_dist_point_le:
	fixes q
	assumes "q \<in> set xs - {p}"
	shows "min_dist_point p xs \<le> dist p q"
proof -
	from assms have "finite (set xs - {p})" 
		by auto
	with assms have "finite ({dist p q |q. q \<in> set xs - {p}})" 
		using finite_imageI[of "set xs - {p}" "\<lambda>q. dist p q"]
		by (metis Setcompr_eq_image)
	then have "finite ({dist p q |q. q \<in> set xs \<and> q \<noteq> p})" 
		by fastforce
	moreover have "q \<noteq> p = (p \<noteq> q)" for q
		by blast
	ultimately have  "finite ({dist p q |q. q \<in> set xs \<and> p \<noteq> q})" 
		by force
	moreover have "dist p q \<in> {dist p q |q. q \<in> set xs \<and> p \<noteq> q}"
		using assms by blast
	ultimately  show ?thesis
		unfolding min_dist_point_def 
		using Min_le by blast
qed

lemma min_dist_eq: 
	assumes "distinct xs" "length xs \<ge> 2" "S = {dist p q | p q. p \<in> set xs \<and> q \<in> set xs \<and> p \<noteq> q}"
	shows "\<forall>d \<in> S. min_dist xs \<le> d"
proof -
	have "finite (set xs \<times> set xs)" 
		by blast
	moreover have "{(p, q) | p q. p \<in> set xs \<and> q \<in> set xs \<and> p \<noteq> q} \<subseteq> set xs \<times> set xs"
		by blast
	ultimately have "finite {(p, q) | p q. p \<in> set xs \<and> q \<in> set xs \<and> p \<noteq> q}"
		using finite_subset by fast
	from finite_imageI[OF this, of "\<lambda>(p, q). dist p q"] have "finite S" 
		by (smt (verit) assms(3) Collect_cong case_prod_conv setcompr_eq_image)
	from assms have "xs \<noteq> []" 
		by auto
	then obtain p where P: "p \<in> set xs" "min_dist xs = min_dist_point p xs" 
		using min_dist_exists by blast
	with assms have "set xs - {p} \<noteq> {}" 
		using length_two_exists by fast
	then obtain q where Q: "q \<in> set xs - {p}""min_dist_point p xs = dist p q"
		using min_dist_point_exists by blast
	then have "\<forall>r \<in> set xs. min_dist_point r xs \<ge> dist p q" 
		using min_dist_le P by metis
	moreover have "\<forall>r \<in> set xs. \<forall> s \<in> set xs - {r}. dist r s \<ge> min_dist_point r xs" 
		using min_dist_point_le by presburger
	ultimately have "\<forall>r \<in> set xs. \<forall> s \<in> set xs - {r}. dist r s \<ge> dist p q"
		using dual_order.trans by blast
	then have "\<forall>r \<in> set xs. \<forall>s \<in> set xs. r \<noteq> s \<longrightarrow>  dist r s \<ge> dist p q"
		by blast
	then have "\<And>y. y \<in> S \<Longrightarrow> dist p q \<le> y" 
		using assms(3)
		by blast
	with P(2) Q(2) show ?thesis by presburger
qed 

lemma min_dist_point_pos: 
	assumes "distinct xs" "length xs \<ge> 2" "p \<in> set xs" 
	shows "min_dist_point p xs > 0"
proof -
	from assms have "set xs - {p} \<noteq> {}"
		using length_two_exists by fast
	then obtain q where "q \<in> set xs - {p}" "dist p q = min_dist_point p xs"
		using min_dist_point_exists by metis 
	then show ?thesis 
		using dist_pos[of p q] by force 
qed 

lemma min_dist_pos: 
	assumes "distinct xs" "length xs \<ge> 2"
	shows "min_dist xs > 0"
proof -
	from assms have "xs \<noteq> []" 
		by force
	then obtain p where  "p \<in> set xs""min_dist xs = min_dist_point p xs"
		using min_dist_exists by blast
	moreover then have "min_dist_point p xs > 0" 
		using min_dist_point_pos assms by blast 
	ultimately show ?thesis by argo
qed


lemma brute_force_dist_nonneg:
"xs \<noteq> [] \<Longrightarrow> brute_force_dist xs \<ge> 0"
	unfolding brute_force_dist_def 
	by (auto simp add: min_list_Min dist_nonneg)

lemma brute_force_dist_correct:
"(p, q) \<in> set xs \<Longrightarrow> brute_force_dist xs \<le> dist p q"
	unfolding brute_force_dist_def 
	by (auto simp add: min_list_Min pair_imageI)

lemma build_pairs_sound: " a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<noteq> b \<Longrightarrow>  (a, b) \<in> set (build_pairs xs) \<or> (b, a) \<in> set (build_pairs xs)"
	by (induction xs rule: build_pairs.induct) auto

lemma build_pairs_complete: 
"\<lbrakk>distinct xs; (a, b) \<in> set (build_pairs xs) \<or> (b, a) \<in> set (build_pairs xs)\<rbrakk> 
		\<Longrightarrow> a \<in> set xs \<and> b \<in> set xs \<and> a \<noteq> b"
	by (induction xs rule: build_pairs.induct) auto

subsection "Grids and Neighbors"

lemma build_grid_sound:
"\<lbrakk>\<lfloor>x/d\<rfloor> = a; \<lfloor>y/d\<rfloor> = b; (x, y) \<in> set xs\<rbrakk> \<Longrightarrow> (x, y) \<in> set (build_grid xs d a b)"
	unfolding build_grid_def 
	by simp

lemma build_grid_complete:
"(x, y) \<in> set (build_grid xs d a b) \<Longrightarrow> (\<lfloor>x/d\<rfloor> = a \<and> \<lfloor>y/d\<rfloor> = b \<and> (x, y) \<in> set xs)"
	unfolding build_grid_def 
	by simp

lemma grid_length_bound_fst_dim:
	assumes "d > 0" "k \<ge> 0" "(x1, y1) \<in> set (build_grid xs d a b1)" "(x2, y2) \<in> set (build_grid xs d (a+2+k) b2)" 
	shows "(x2 - x1) > d"
proof -
	from assms have "\<lfloor>x1/d\<rfloor> = a" "\<lfloor>x2/d\<rfloor> = a + 2 + k"
		using build_grid_complete by blast+
	then have "x1 < (a + 1) * d" "x2 \<ge> (a + 2 + k) * d"
		using floor_divide_upper assms(1)  apply force 
		using floor_divide_lower assms(1) \<open>\<lfloor>x2/d\<rfloor> = a + 2 + k\<close> by metis
	then have "(a + 2 + k) * d - (a + 1) * d  < x2 - x1" 
		by simp
	moreover have "d \<le> d + k * d" 
		using assms by auto
	ultimately show ?thesis 
		by (simp add: distrib_left mult.commute)
qed 

lemma grid_length_bound_snd_dim:
  assumes "d > 0" "k \<ge> 0" "(x1, y1) \<in> set (build_grid xs d a1 b)" "(x2, y2) \<in> set (build_grid xs d a2 (b+2+k))" 
	shows "(y2 - y1) > d"
proof -
	from assms have "\<lfloor>y1/d\<rfloor> = b" "\<lfloor>y2/d\<rfloor> = b + 2 + k"
		using build_grid_complete by blast+
	then have "y1 < (b + 1) * d" "y2 \<ge> (b + 2 + k) * d"
		using floor_divide_upper assms(1)  apply force 
		using floor_divide_lower assms(1) \<open>\<lfloor>y2/d\<rfloor> = b + 2 + k\<close> by metis
	then have "(b + 2 + k) * d - (b + 1) * d  < y2 - y1" 
		by simp
	moreover have "d \<le> d + k * d" 
		using assms by auto
	ultimately show ?thesis 
		by (simp add: distrib_left mult.commute)
qed     

lemma neighbors_subset: "set (neighbors_of_point xs d a b) \<subseteq> set xs"
	unfolding neighbors_of_point_def build_grid_def by auto

lemma neighborhood_subset: "set (neighborhood xs d x y) \<subseteq> set xs"
	unfolding neighborhood_def 
	using neighbors_subset by force

lemma neighbors_distinct: "distinct xs \<Longrightarrow> distinct (neighbors_of_point xs d a b)" 
	unfolding neighbors_of_point_def build_grid_def by auto

lemma neighborhood_distinct: "distinct xs \<Longrightarrow> distinct (neighborhood xs d x y)" 
	unfolding neighborhood_def 
	using neighbors_distinct by force

lemma dist_of_non_neighborhood:
	assumes "d > 0" "p \<in> set xs" "q \<in> set xs" "q \<notin> set (neighbors_of_point xs d \<lfloor>fst p / d\<rfloor> \<lfloor>snd p / d\<rfloor>)"
	shows  "dist p q > d"
proof -
	obtain a1 b1 a2 b2 where AB:
		"a1 = \<lfloor>fst p / d\<rfloor>" "b1 = \<lfloor>snd p / d\<rfloor>"
		"a2 = \<lfloor>fst q / d\<rfloor>" "b2 = \<lfloor>snd q / d\<rfloor>"
		by blast
	have A: "(fst p, snd p) \<in> set (build_grid xs d a1 b1)"
		by (metis prod.collapse build_grid_sound assms(2) AB(1, 2)) 
	have B: "(fst q, snd q) \<in> set (build_grid xs d a2 b2)" 
		by (metis prod.collapse build_grid_sound assms(3) AB(3, 4)) 
	then consider "a1 \<ge> a2 + 2" | "a1 \<le> a2 - 2" | "b1 \<ge> b2 + 2" | "b1 \<le> b2 - 2" 
		using assms(4)
		unfolding neighbors_of_point_def 
		apply (auto simp add: build_grid_sound AB)
		by (smt (verit, del_insts))
	then show ?thesis 
	proof cases
		case 1
		then have "\<exists>k. a2 + 2 + k = a1 \<and> k \<ge> 0" 
			by presburger
		then obtain k where "a1 = a2 + 2 + k" "k \<ge> 0" 
			by blast
		then have "d < fst p - fst q"
			using grid_length_bound_fst_dim[OF assms(1)] A B by blast
		also have "... = sqrt (fst p - fst q)^2"
			using assms(1) calculation by auto
		also then have "... \<le> sqrt ((fst p - fst q)^2 + (snd p - snd q)^2)"
			by force
		finally show ?thesis 
			by (metis dist.simps prod.collapse)
	next
		case 2
		then have "\<exists>k. a1 + 2 + k = a2 \<and> k \<ge> 0" 
			by presburger
		then obtain k where "a2 = a1 + 2 + k" "k \<ge> 0" 
			by blast
		then have "d < fst q - fst p"
			using grid_length_bound_fst_dim[OF assms(1)] A B by blast
		also have "... = sqrt (fst q - fst p)^2"
			using assms(1) calculation by auto
		also then have "... \<le> sqrt ((fst q - fst p)^2 + (snd p - snd q)^2)"
			by force
		also have "... = sqrt ((fst p - fst q)^2 + (snd p - snd q)^2)"
			by (simp add: power2_commute)
		finally show ?thesis 
			by (metis dist.simps prod.collapse)
	next
		case 3
		then have "\<exists>k. b2 + 2 + k = b1 \<and> k \<ge> 0" 
			by presburger
		then obtain k where "b1 = b2 + 2 + k" "k \<ge> 0" 
			by blast
		then have "d < snd p - snd q"
			using grid_length_bound_snd_dim[OF assms(1)] A B by blast
		also have "... = sqrt (snd p - snd q)^2"
			using assms(1) calculation by auto
		also then have "... \<le> sqrt ((fst p - fst q)^2 + (snd p - snd q)^2)"
			by force
		finally show ?thesis 
			by (metis dist.simps prod.collapse)
	next
		case 4
		then have "\<exists>k. b1 + 2 + k = b2 \<and> k \<ge> 0" 
			by presburger
		then obtain k where "b2 = b1 + 2 + k" "k \<ge> 0" 
			by blast
		then have "d < snd q - snd p"
			using grid_length_bound_snd_dim[OF assms(1)] A B by blast
		also have "... = sqrt (snd q - snd p)^2"
			using assms(1) calculation by auto
		also then have "... \<le> sqrt ((fst p - fst q)^2 + (snd q - snd p)^2)"
			by force
		also have "... = sqrt ((fst p - fst q)^2 + (snd p - snd q)^2)"
			by (simp add: power2_commute)
		finally show ?thesis 
			by (metis dist.simps prod.collapse)
	qed 
qed

lemma neighborhood_nonempty: 
	assumes "d > 0" "(x, y) \<in> set ps" "set ps - {(x, y)} \<noteq> {}" "min_dist_point (x, y) ps \<le> d" 
	shows "neighborhood ps d x y \<noteq> []"
proof -
	have "\<exists>q \<in> set ps - {(x, y)}. dist (x, y) q = min_dist_point (x, y) ps"
		using min_dist_point_exists[of ps] assms(3) by metis
	then obtain q where A: "q \<in> set ps - {(x, y)}" "dist (x, y) q = min_dist_point (x, y) ps"
		by blast
	then have "dist (x, y) q \<le> d" 
		using assms(4) by simp
	then have "q \<in> set (neighbors_of_point ps d \<lfloor>x / d\<rfloor> \<lfloor>y / d\<rfloor>)" 
		using dist_of_non_neighborhood[OF assms(1) assms(2)] A(1) 
		by fastforce
	then have "q \<in> set (neighborhood ps d x y)"
		unfolding neighborhood_def 
		using A(1) by auto
	then show ?thesis by force
qed

lemma dist_of_neighbors:
	assumes "d > 0" "(x', y') \<in> set (neighborhood xs d x y)" 
	shows "dist (x, y) (x', y') \<le> sqrt (8 * d^2)"
proof -
	let ?a = "\<lfloor>x/d\<rfloor>" let ?b = "\<lfloor>y/d\<rfloor>"
	let ?xg = "{?a - 1, ?a, ?a + 1}" let ?yg = "{?b - 1, ?b, ?b + 1}"
	have A: "?a * d \<le> x" "(?a + 1) * d > x"
		using assms(1) floor_divide_lower floor_divide_upper by auto
	have B: "?b * d \<le> y" "(?b + 1) * d > y" 
		using assms(1) floor_divide_lower floor_divide_upper by auto
	obtain a' b' where C: "a' = \<lfloor>x' / d\<rfloor>" "b' = \<lfloor>y' / d\<rfloor>"
		by blast
	have "\<exists>a' b'. a' \<in> ?xg \<and> b' \<in> ?yg \<and> (x', y') \<in> set (build_grid xs d a' b')"
	 	 using assms(2)
	 	 unfolding neighborhood_def neighbors_of_point_def 
	 	 by auto
	then obtain a'' b'' where D: "a'' \<in> ?xg" "b'' \<in> ?yg" "(x', y') \<in> set (build_grid xs d a'' b'')"
		by blast
	then have "a'' = a'" "b'' = b'" 
		using build_grid_complete C by metis+
	then have E: "a' \<in> ?xg" "b' \<in> ?yg"
		using D by simp+
	then have x'_bound: "(?a - 1) * d \<le> x' \<and> (?a + 2) * d > x'"
	proof -
		consider "a' = ?a-1" | "a' = ?a" | "a' = ?a + 1" 
			using E by blast
		then show ?thesis 
			by (cases; smt (verit, best) assms(1) floor_less_iff pos_le_divide_eq C)
	qed
	from E have y'_bound: "(?b - 1) * d \<le> y' \<and> (?b + 2) * d > y'"
	proof -
		consider "b' = ?b-1" | "b' = ?b" | "b' = ?b + 1" 
			using E by blast
		then show ?thesis 
			by (cases; smt (verit, best) assms(1) floor_less_iff pos_le_divide_eq C)
	qed

	from A x'_bound have "x - x' \<le> d * (?a+1) - d * (?a-1)"
		by argo
	also have "... = d * ?a + d - d * (?a-1)"
		by (simp add: distrib_left)
	also have "... = d * ?a + d - d * ?a + d"
		by (simp add: distrib_left, argo)
	also have "... = 2 * d"
		by argo
	finally have 1: "x - x' \<le> 2 * d" .

	from A x'_bound have "x' - x \<le> d * (?a+2) - d * ?a"
		by argo
	also have "... = d * ?a + 2 * d - d * ?a"
		by (simp add: distrib_left)
	also have "... = 2 * d"
		by argo
	finally have 2: "x' - x \<le> 2 * d" .

	from B y'_bound have "y - y' \<le> d * (?b+1) - d * (?b-1)"
		by argo
	also have "... = d * ?b + d - d * (?b-1)"
		by (simp add: distrib_left)
	also have "... = d * ?b + d - d * ?b + d"
		by (simp add: distrib_left, argo)
	also have "... = 2 * d"
		by argo
	finally have 3: "y - y' \<le> 2 * d" .

	from B y'_bound have "y' - y \<le> d * (?b+2) - d * ?b"
		by argo
	also have "... = d * ?b + 2 * d - d * ?b"
		by (simp add: distrib_left)
	also have "... = 2 * d"
		by argo
	finally have 4: "y' - y \<le> 2 * d" .

	from 1 2 have "(x - x')^2 \<le> (2 * d)^2"
		by (metis diff_ge_0_iff_ge linorder_linear power2_commute power_mono)
	moreover from 3 4 have "(y - y')^2 \<le> (2 * d)^2"
		by (metis diff_ge_0_iff_ge linorder_linear power2_commute power_mono)
	ultimately have "dist (x, y) (x', y') \<le> sqrt ( (2 * d)^2 +  (2 * d)^2)"
		by auto
	also have "... = sqrt (4 * d^2 + 4 * d^2)"
		by force
	finally show ?thesis 
		by argo
qed 

lemma find_in_grids_min:
	assumes "d > 0" "(x, y) \<in> set xs"  "neighborhood xs d x y \<noteq> []"
	shows ForAll: "\<forall>s \<in> set (neighborhood xs d x y). find_in_grids xs d (x, y) \<le> dist (x, y) s"
	and		Exists: "\<exists>r \<in> set (neighborhood xs d x y). find_in_grids xs d (x, y) = dist (x, y) r"
proof -
	let ?neighbors = "neighborhood xs d x y"
	have 1: "finite (set ?neighbors)" "set ?neighbors \<noteq> {}"
			using assms(3) by auto
		then have 2: "(map (\<lambda>(x, y). dist x y) 
			(map (Pair (x, y)) (neighborhood xs d x y))) \<noteq> []"
			by blast
		from 1 have 3: "\<And>f. f ` set ?neighbors \<noteq> {}" 
			by blast
		from min_list_Min[OF 2] show  
			"\<forall>s \<in> set (neighborhood xs d x y). find_in_grids xs d (x, y) \<le> dist (x, y) s"
			unfolding find_in_grids_def Let_def
			using 1 by auto
		show "\<exists>r \<in> set ?neighbors. find_in_grids xs d (x, y) = dist (x, y) r"
			unfolding find_in_grids_def Let_def 
			using  min_list_Min[OF 2] Min_in[OF finite_imageI[OF 1(1)] 3] 
			by auto
qed 

(*this lemma needs refinement*)
lemma find_in_grids_correct_one:
	assumes "d > 0" "(x, y) \<in> set xs" "neighborhood xs d x y \<noteq> []" 
		"find_in_grids xs d (x, y) \<le> d" 
	shows "find_in_grids xs d (x, y) = min_dist_point (x, y) xs"
proof -
	let ?neighbors = "neighborhood xs d x y"
	have A: "\<forall>q \<in> set xs - set ?neighbors - {(x, y)}. dist (x, y) q > d" 
		unfolding neighborhood_def
		using dist_of_non_neighborhood[OF assms(1, 2)] by auto
	have "\<exists>q \<in> set ?neighbors. dist (x, y) q \<le> d" 
		using assms(3, 4)
		unfolding find_in_grids_def Let_def
		apply (auto split: if_split simp: min_list_Min)
		by (metis arg_min_list_in f_arg_min_list_f)
	then have "\<exists>q \<in> set xs - {(x, y)}. dist (x, y) q \<le> d" "set xs - {(x, y)} \<noteq> {}"
		using neighborhood_subset assms(3)
		unfolding neighborhood_def
		by force+
	then obtain q where B: "q \<in> set xs - {(x, y)}" "dist (x, y) q \<le> d" 
		by blast
	have "finite {p \<in> set xs. (x, y) \<noteq> p}" "{p \<in> set xs. (x, y) \<noteq> p} \<noteq> {}"
		using \<open>set xs - {(x, y)} \<noteq> {}\<close> by auto
	then have C: "finite {dist (x, y) q | q. q \<in> set xs \<and> (x, y) \<noteq> q}"
		"{dist (x, y) q | q. q \<in> set xs \<and> (x, y) \<noteq> q} \<noteq> {}"
			using finite_image_set by blast+
	then have "min_dist_point (x, y) xs \<le> dist (x, y) q"
		unfolding min_dist_point_def 
		using Min_le B by blast
	then have D: "min_dist_point (x, y) xs \<le> d"
		using B by argo
	from C have  "\<exists>r \<in> set xs - {(x, y)}.  min_dist_point (x, y) xs = dist (x, y) r" 
		unfolding min_dist_point_def 
		using  Min_in by blast
	then obtain r where E: "r \<in> set xs - {(x, y)}" "min_dist_point (x, y) xs = dist (x, y) r" 
		by blast
	then have "\<forall>s \<in> set xs - {(x, y)}. dist (x, y) r \<le> dist (x, y) s"
		using Min_le C
		unfolding min_dist_point_def by fastforce
	moreover have "set ?neighbors \<subseteq> set xs - {(x, y)}"
		using neighborhood_subset unfolding neighborhood_def 
		by force
	ultimately have "\<forall>s \<in> set ?neighbors. dist (x, y) r \<le> dist (x, y) s" 
		by blast
	moreover have "r \<in> set ?neighbors"
		using A D E by force
	ultimately have "find_in_grids xs d (x, y) = dist (x, y) r"
	proof -
		assume prems: 
			"\<forall>s \<in> set ?neighbors. dist (x, y) r \<le> dist (x, y) s" 
			"r \<in> set ?neighbors"
		have 
		"\<forall>s \<in> set ?neighbors. find_in_grids xs d (x, y) \<le> dist (x, y) s"
		"\<exists>r \<in> set ?neighbors. find_in_grids xs d (x, y) = dist (x, y) r"
			 using find_in_grids_min assms by blast+
		 then show "find_in_grids xs d (x, y) = dist (x, y) r" 
			using prems by fastforce
	qed
	then show ?thesis 
		using E by auto
qed 

lemma find_in_grids_correct_two:
	assumes "d > 0" "(x, y) \<in> set xs" "neighborhood xs d x y \<noteq> []" 
		"find_in_grids xs d (x, y) > d"
	shows "min_dist_point (x, y) xs > d"
proof -
	let ?neighbors = "neighborhood xs d x y"
	have "\<forall>q \<in> set ?neighbors. find_in_grids xs d (x, y) \<le> dist (x, y) q"
		using find_in_grids_min assms by blast
	then have "\<forall>q \<in> set ?neighbors. d < dist (x, y) q"
		using assms(4) by fastforce
	moreover have "\<forall>q \<in> set xs - set ?neighbors - {(x, y)}. dist (x, y) q > d" 
		unfolding neighborhood_def
		using dist_of_non_neighborhood[OF assms(1, 2)] by auto
	ultimately have A: "\<forall>q \<in> set xs - {(x, y)}. dist (x, y) q > d" 
		by blast
	have "(x, y) \<notin> set ?neighbors" 
		unfolding neighborhood_def 
		by fastforce
	then have "set ?neighbors - {(x, y)} \<noteq> {}"
		using assms(3) by auto
	then have "set xs - {(x, y)} \<noteq> {} "
		using neighborhood_subset[of xs d x y] by blast
	then have B: "Min (dist (x, y) ` (set xs - {(x, y)})) > d" 
	 	 using Min_le A by simp
	have "{q | q. q \<in> set xs \<and> (x, y) \<noteq> q} = set xs - {(x, y)}"
		by blast
	then have "dist (x, y) ` (set xs - {(x, y)}) = 
		{dist (x, y) q| q. q \<in> set xs \<and> (x, y) \<noteq> q}"
		by blast
	then show ?thesis 
		unfolding min_dist_point_def 
		using B by presburger
qed

theorem traverse_grids_correct: 
	assumes "d > 0" "distinct xs" "length xs \<ge> 2" "d \<ge> min_dist xs"
	shows "traverse_grids xs d = min_dist xs"
proof -
	from assms(3) have "\<exists>p \<in> set xs.  min_dist xs = min_dist_point p xs"
		using min_dist_exists[of xs] by fastforce
	then obtain x y where A: "(x, y) \<in> set xs" "min_dist xs = min_dist_point (x, y) xs" 
		"min_dist_point (x, y) xs \<le> d"
		using assms(4) by auto
	then have "set xs - {(x, y)} \<noteq> {}" 
		using length_two_exists
	 	using assms(2, 3) by fast
	then have B: "neighborhood xs d x y \<noteq> []" 
		using neighborhood_nonempty[OF assms(1) A(1) _ A(3)] 
		by fastforce
	have C: "finite (set ((filter ((<) 0)) (map f xs)))" for f
		using assms(3) by auto
	consider "find_in_grids xs d (x, y) > d" | "find_in_grids xs d (x, y) \<le> d" 
		by argo
	then show ?thesis 
	proof cases
		case 1
		then show ?thesis
			using find_in_grids_correct_two assms A B by fastforce
	next
		case 2
		let ?d = "find_in_grids xs d (x, y)"
		have  D: "?d = min_dist xs"
			using find_in_grids_correct_one[OF assms(1) A(1) B 2] A(2) by presburger
		have "\<And>x' y'.\<lbrakk>(x', y') \<in> set xs; find_in_grids xs d (x', y') > 0\<rbrakk> \<Longrightarrow> find_in_grids xs d (x', y') \<ge> ?d"
		proof -
			fix x' y'
			assume prems: "(x', y') \<in> set xs" "find_in_grids xs d (x', y') > 0"
			show "find_in_grids xs d (x', y') \<ge> ?d"
			proof (cases "find_in_grids xs d (x', y') \<ge> d")
				case True
				then show ?thesis
					using find_in_grids_correct_two assms A B by fastforce 
			next
				case outer: False 
				then show ?thesis
					proof (cases "neighborhood xs d x' y' = []")
						case True
						then have "find_in_grids xs d (x', y') = 0"
							unfolding find_in_grids_def Let_def  by simp
						then show ?thesis
							 using prems(2) by simp
					next
						case False
						have "find_in_grids xs d (x', y') = min_dist_point (x', y') xs"
							using find_in_grids_correct_one[OF assms(1) prems(1) False] outer 
							by auto
						moreover have "min_dist_point (x', y') xs \<ge>  min_dist_point (x, y) xs"
							using A(1, 2) prems(1) min_dist_le by force
						ultimately show ?thesis 
							using D A(2) by presburger
					qed
			qed
		qed 
		then have "(\<And>y. y \<in> set (filter ((<) 0) (map (find_in_grids xs d) xs)) \<Longrightarrow> ?d \<le> y)"
			by auto
		moreover have "?d \<in> set (filter ((<) 0) (map (find_in_grids xs d) xs))"
			using A(1) D min_dist_pos[of xs] assms by force
		ultimately have 
			"filter ((<) 0) (map (find_in_grids xs d) xs) \<noteq> []"
			"Min (set (filter ((<) 0) (map (find_in_grids xs d) xs))) = ?d"
			using Min_eqI[OF C(1)[of "find_in_grids xs d"], of ?d] by force+ 
		then have "traverse_grids xs d = ?d"
			unfolding traverse_grids_def 
			using min_list_Min[of "filter ((<) 0) (map (find_in_grids xs d) xs)"] 
			by presburger
		 then show ?thesis using D by presburger
	qed 
qed

section "randomized implementation"

definition first_phase :: "point list \<Rightarrow> real pmf" where 
"first_phase ps = do {
	xs \<leftarrow> replicate_pmf (length ps) (pmf_of_set (set (build_pairs ps)));
	return_pmf (brute_force_dist xs)
}"

definition closest_pair :: "point list \<Rightarrow> real pmf" where 
"closest_pair ps = do {
	d \<leftarrow> first_phase ps;
	return_pmf (min d (traverse_grids ps d))
}"

theorem first_phase_correct:
	fixes d 
	assumes "distinct ps" "length ps \<ge> 2" "d = min_dist ps" 
	shows "measure (first_phase ps) {x. x \<ge> d} = 1"
proof -
	from assms(2) have "\<exists>a b qs. ps = a # b # qs" 
		by (metis One_nat_def Suc_1 Suc_le_length_iff)
	then obtain a b qs where "ps = a # b # qs" 
		by blast
	with assms(1) have "a \<noteq> b" "a \<in> set ps" "b \<in> set ps"
		by auto 
  then have A: "set (build_pairs ps) \<noteq> {}" "finite (set (build_pairs ps))" 
  	using build_pairs_sound by fastforce+ 

  have "x \<ge> d" if "x \<in> set_pmf (first_phase ps)" for x
  proof -
  	let ?S = "{dist p q |p q. p \<in> set ps \<and> q \<in> set ps \<and> p \<noteq> q}"
    from that
    obtain y where B: "y \<in> lists (set (build_pairs ps))" 
    			"length y = length ps" "x = brute_force_dist y"
      unfolding first_phase_def by (simp add:set_replicate_pmf set_pmf_of_set[OF A]) blast
    then have "set (map (\<lambda>(x, y). dist x y) y) \<noteq> {}" "map (\<lambda>(x, y). dist x y) y \<noteq> []"
    	using assms(2) by auto
    moreover have "finite (set (map (\<lambda>(x, y). dist x y) y))"
    	using B by blast
    ultimately have "x \<in> set (map (\<lambda>(x, y). dist x y) y)"
    	using B(3) min_list_Min[of "map (\<lambda>(x, y). dist x y) y"]
    			Min_in[of "set (map (\<lambda>(x, y). dist x y) y)"] 
    	unfolding brute_force_dist_def by force
    then have "\<exists>u v. (u, v) \<in> set y \<and> x = dist u v"
    	using B by fastforce
    then obtain u v where C: "(u,v) \<in> set y" "x = dist u v"
    	by blast
    then have "(u, v) \<in> set (build_pairs ps)"
    	using B by blast
    then have "u \<in> set ps" "v \<in> set ps" "u \<noteq> v" 
    	using build_pairs_complete assms(1)  by blast+
    then have "dist u v \<in> ?S" 
    	by blast
    then have "dist u v \<ge> d" 
    	using min_dist_eq assms by presburger
    then show ?thesis 
    	using C by blast
  qed
  hence "AE x in first_phase ps. x \<ge> d" using AE_pmfI by auto
  thus ?thesis
    using measure_pmf.prob_Collect_eq_1 by fastforce
qed

theorem closest_pair_correct:
	assumes "distinct ps" "length ps \<ge> 2" "d = min_dist ps"
	shows "measure (closest_pair ps) {d} = 1" (is "?L = ?R")
proof -
	let ?d = "first_phase ps"
	have "\<And>x. x \<ge> d \<Longrightarrow> traverse_grids ps x = d"
	proof -
		fix x
		assume "x \<ge> d"
		then have "x > 0" "x \<ge> min_dist ps"
			using assms min_dist_pos by force+
		then show "traverse_grids ps x = d" 
			using assms traverse_grids_correct[of x ps]
			by blast
	qed
	then have A: "{x. min x (traverse_grids ps x) = d} \<supseteq> {x. x \<ge> d}"
		unfolding min_def by auto
	have "?R = measure ?d {x. x \<ge> d}"
		using first_phase_correct assms by presburger
	also have "... \<le> measure ?d {x. min x (traverse_grids ps x) = d}"
		by (simp add: A measure_pmf.finite_measure_mono)
	finally have "measure ?d {x. min x (traverse_grids ps x) = d} = 1"
		by (simp add: measure_pmf.measure_ge_1_iff)
	then show ?thesis 
		by (simp add: closest_pair_def map_pmf_def[symmetric] vimage_def) 
qed 


end 