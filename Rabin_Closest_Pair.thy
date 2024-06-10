theory Rabin_Closest_Pair 
  imports "HOL-Probability.Probability_Mass_Function" Complex_Main
begin
  
(* We verify Rabin's closest pair algorithm in 2D Euclidean space *)

section "Preliminaries"

type_synonym point = "real * real"

fun dist :: "point => point => real" where 
"dist (x1, y1) (x2, y2) = sqrt ((x1 - x2)^2 + (y1 - y2)^2)"

lemma dist_compact_on_finite: "p \<notin> set (x # xs) \<Longrightarrow> \<exists>q \<in> set (x # xs). \<forall>r \<in> set (x # xs). dist p q \<le> dist p r"
proof (induction xs arbitrary: x)
  case (Cons a xs)
  hence " \<exists>q\<in>set (a # xs). \<forall>r\<in>set (a # xs). dist p q \<le> dist p r"
    by simp 
  then obtain q where "q \<in> set (a # xs)" "\<forall>r\<in>set (a # xs). dist p q \<le> dist p r"
    by blast 
  then show ?case
    by (cases "dist p q \<le> dist p x") auto
qed auto

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

lemma dist_pos_rev: "dist p q > 0 \<Longrightarrow> p \<noteq> q"
proof -
	assume "dist p q > 0"
	then have "(fst p - fst q)^2 + (snd p - snd q)^2 > 0" 
		by (metis dist.simps real_sqrt_eq_0_iff real_sqrt_less_iff surjective_pairing)
	then show "p \<noteq> q" by auto
qed 


fun brute_force_dist :: "(point * point) list => real" where 
"brute_force_dist [] = -1" |
"brute_force_dist (x#xs) = (
    let dist' = brute_force_dist xs; curr = dist (fst x) (snd x) in 
    (if dist' < curr \<and> dist' \<ge> 0 then dist' 
     else curr)
     )"

lemma brute_force_dist_exists: "points \<noteq> []  \<Longrightarrow> \<exists>(p, q) \<in> set points. brute_force_dist points = dist p q"
proof (induction points)
  case (Cons a points)
  then show ?case by (induction points arbitrary: a) (auto simp del: dist.simps simp add: Let_def)
qed simp

lemma brute_force_dist_pos: "ps \<noteq> [] \<Longrightarrow> brute_force_dist ps \<ge> 0"
	sledgehammer
	by (smt (verit, ccfv_threshold) brute_force_dist.elims dist_nonneg)

lemma brute_force_dist_strict_pos: 
	assumes "\<forall>(p, q) \<in> set ps. p \<noteq> q" "ps \<noteq> []" 
	shows "brute_force_dist ps > 0"
proof -
	have "\<forall>(p, q) \<in> set ps. dist p q > 0"
		using assms(1) dist_pos by blast
	with assms(2) show ?thesis
	proof (induction ps)
		case (Cons a as)
		then show ?case 
		proof (cases as)
			case Nil
			then show ?thesis
				using Cons by fastforce
		next
			case (Cons b bs)
			then have "\<forall>(p, q) \<in> set as. 0 < Rabin_Closest_Pair.dist p q \<Longrightarrow> 0 < brute_force_dist as"
				using Cons.IH by blast
			with Cons.prems have "brute_force_dist as > 0" by simp
			moreover have "dist (fst a) (snd a) > 0" 
				using Cons Cons.prems by auto
			ultimately show ?thesis by (auto simp: Let_def)
		qed 
	qed simp
qed

theorem brute_force_dist_correct: "(p, q) \<in> set points  \<Longrightarrow> dist p q \<ge> brute_force_dist points"
	apply (induction points)
	 apply (auto simp del: dist.simps simp add: Let_def brute_force_dist_pos)
	by (metis brute_force_dist_pos ex_in_conv list.set(1))

fun build_pairs :: "point list => (point * point) list" where 
"build_pairs [] = []" |
"build_pairs (x#xs) = (map (\<lambda>a. (x, a)) xs) @ build_pairs xs"

lemma build_pairs_sound: " a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<noteq> b \<Longrightarrow>  (a, b) \<in> set (build_pairs xs) \<or> (b, a) \<in> set (build_pairs xs)"
	by (induction xs) auto

lemma build_pairs_complete: "(a, b) \<in> set (build_pairs xs) \<or> (b, a) \<in> set (build_pairs xs) \<Longrightarrow> a \<in> set xs \<and> b \<in> set xs"
	by (induction xs) auto

section "Grid Map"


(* Squares in 2D space can be represented with two end points.
   Since grid length is fixed, we simply need the initial point for representation,
   hence we store them in a list of list *)


type_synonym grid = "point list"
type_synonym grid_map = "int \<Rightarrow> int => grid"

(*
a grid is a list that stores all points
a grid map is a function from the index of the left-lower point to the grid
*)

fun build_grid_map :: "point list  => real => grid_map => grid_map" where 
"build_grid_map [] d m = m" |
"build_grid_map (a#as) d m = 
  (let x = \<lfloor>(fst a) / d\<rfloor>; y = \<lfloor>(snd a) / d\<rfloor>;
       m' = build_grid_map as d m
  in 
    (\<lambda>z1 z2. if z1 = x \<and> z2 = y then remdups (a # (m' z1 z2)) else m' z1 z2)
  )"

lemma build_grid_map_sound:
  assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "p \<in> set xs"
  shows "p \<in> set (m \<lfloor>(fst p)/ d\<rfloor>  \<lfloor>(snd p) / d\<rfloor>)"
  using assms apply (induction xs arbitrary: p m)
  by  (auto simp: Let_def; force)+

lemma build_grid_map_complete:
  assumes  "m = build_grid_map xs d (\<lambda>_ _. [])"
  shows "p \<in> set (m x y) \<Longrightarrow> (x = \<lfloor>(fst p)/ d\<rfloor> \<and> y = \<lfloor>(snd p) / d\<rfloor> \<and> p \<in> set xs)"
using assms proof (induction xs arbitrary: p m x y)
  case (Cons a xs)
  obtain m' where m'_def: "m' = build_grid_map xs d (\<lambda>_ _. [])"
    by blast 
  hence aux1: "m = build_grid_map [a] d m'" 
    by (auto simp: Let_def Cons(3))
  hence aux2: "m x y = remdups (a # m' x y) \<or> m' x y = m x y" 
    by auto
  then show ?case 
    proof (cases "m' x y")
      case Nil
      hence "m x y = [p]" "m x y = [a]"
        using Cons(2) aux2 by fastforce+
      hence "a = p" 
        by force
      moreover have "x = \<lfloor>fst a / d\<rfloor> \<and> y = \<lfloor>snd a / d\<rfloor>"
        using aux1 \<open>m x y = [a]\<close> Nil not_Cons_self2 by fastforce
      ultimately show ?thesis by force
    next
      case (Cons b bs)
      then obtain q where "q \<in> set (m' x y)" 
        by fastforce
      then have "x = \<lfloor>fst q / d\<rfloor> \<and> y = \<lfloor>snd q / d\<rfloor> \<and> q \<in> set xs"
        by (simp add: Cons.IH m'_def assms(1))
      then show ?thesis 
      	by (smt (verit, best) Cons.IH Cons.prems(1) aux1 build_grid_map.simps(1) build_grid_map.simps(2) 
      			insert_iff list.set(2) m'_def set_remdups)
    qed
qed simp

thm floor_divide_lower floor_divide_upper

definition "neighbors m x y \<equiv> 
       m x y @ (m (x + 1) y) @ (m (x - 1) y) @ (m x (y + 1)) @ (m x (y - 1)) 
      @ (m (x + 1) (y + 1)) @ (m (x + 1) (y - 1)) @ (m (x - 1) (y + 1)) @ (m (x - 1) (y - 1))"

definition "in_map p m \<equiv> \<exists>x y. p \<in> set (m x y)"

lemma dist_of_non_neighbors :
  assumes "p \<in> set (m x y)" "m = build_grid_map xs d (\<lambda>_ _. [])" "d > 0"
  shows "in_map (a, b) m \<and> (a, b) \<notin> set (neighbors m x y) \<longrightarrow> dist p (a, b) \<ge> d"
proof
    fix  a b
    let ?x' = "\<lfloor>a / d\<rfloor>" let ?y' = "\<lfloor>b / d\<rfloor>"
    let ?x1 = "fst p" let ?y1 = "snd p" 
    have "\<forall>x1 y1. (a, b) \<in> set (m x y)\<longrightarrow> x = ?x' \<and> y = ?y'"
      using assms build_grid_map_complete by force
    moreover assume "in_map (a, b) m \<and> (a, b) \<notin> set (neighbors m x y)"
    ultimately consider "?x' < x - 1" | "?x' > x + 1" | "?y' < y - 1" | "?y' > y + 1"
      unfolding in_map_def neighbors_def apply auto 
      by (smt (verit, ccfv_SIG) assms(2) build_grid_map_complete prod.sel(1) prod.sel(2))
    then show "d \<le> dist p (a, b)"
    proof cases
      case 1
      then have "\<lfloor>a / d\<rfloor> \<le> x - 2"
        by simp
      then have "\<lfloor>a / d \<rfloor> * d \<le> (x - 2) * d"
        using assms(3) by fastforce
      moreover have "a - d \<le> \<lfloor>a / d \<rfloor> * d" 
        by (smt (verit, best) assms(3) divide_diff_eq_iff less_divide_eq_1_pos real_of_int_floor_ge_diff_one)
      ultimately have "a - d \<le> (x - 2) * d"
        by argo  
      hence "a \<le> (x - 2) * d + d" 
        by argo
      hence "a \<le> x * d - d"
        by (simp add: mult.commute right_diff_distrib)
      moreover have "x * d \<le> ?x1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_lower[OF assms(3)] 
        by fast
      ultimately have "d \<le> ?x1 - a" 
        by argo
      also have "... \<le> sqrt ((?x1 - a)^2 + (?y1 - b)^2)" 
        by auto
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    next
      case 2
      then have "\<lfloor>a / d \<rfloor> * d \<ge> (x + 2) * d"
        using assms(3) by fastforce
      moreover have "a  \<ge> \<lfloor>a / d\<rfloor> * d" 
        using floor_divide_lower assms(3) by blast 
       ultimately have "a \<ge> (x + 2) * d"
        by argo  
      hence "a \<ge> (x + 1) * d + d" 
        by (simp add: distrib_left mult.commute)
      moreover have "(x + 1) * d > ?x1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_upper[OF assms(3)] 
        by force
      ultimately have "d \<le> a - ?x1" 
        by argo
      also have "... \<le> sqrt ((a - ?x1)^2 + (?y1 - b)^2)" 
        by auto
      also have "... \<le> sqrt ((?x1 - a )^2 + (?y1 - b)^2)"
        by (simp add: power2_commute)
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    next
      case 3
      then have "\<lfloor>b / d\<rfloor> \<le> y - 2"
        by simp
      then have "\<lfloor>b / d \<rfloor> * d \<le> (y - 2) * d"
        using assms(3) by fastforce
      moreover have "b - d \<le> \<lfloor>b / d \<rfloor> * d" 
        by (smt (verit, best) assms(3) divide_diff_eq_iff less_divide_eq_1_pos real_of_int_floor_ge_diff_one)
      ultimately have "b - d \<le> (y - 2) * d"
        by argo  
      hence "b \<le> (y - 2) * d + d" 
        by argo
      hence "b \<le> y * d - d"
        by (simp add: mult.commute right_diff_distrib)
      moreover have "y * d \<le> ?y1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_lower[OF assms(3)] 
        by fast
      ultimately have "d \<le> ?y1 - b" 
        by argo
      also have "... \<le> sqrt ((?x1 - a)^2 + (?y1 - b)^2)" 
        by auto
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    next
      case 4
      then have "\<lfloor>b / d \<rfloor> * d \<ge> (y + 2) * d"
        using assms(3) by fastforce
      moreover have "b  \<ge> \<lfloor>b / d\<rfloor> * d" 
        using floor_divide_lower assms(3) by blast 
       ultimately have "b \<ge> (y + 2) * d"
        by argo  
      hence "b \<ge> (y + 1) * d + d" 
        by (simp add: distrib_left mult.commute)
      moreover have "(y + 1) * d > ?y1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_upper[OF assms(3)] 
        by force
      ultimately have "d \<le> b - ?y1" 
        by argo
      also have "... \<le> sqrt ((b - ?y1)^2 + (?x1 - a)^2)" 
        by auto
      also have "... \<le> sqrt ((?x1 - a )^2 + (?y1 - b)^2)"
        by (simp add: power2_commute)
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    qed
  qed


lemma nearest_in_neighbors: 
  assumes "p \<in> set (m x y)" "set (neighbors m x y) - {p} \<noteq> {}" "m = build_grid_map xs d (\<lambda>_ _. [])" "d > 0"
  shows "\<exists>q \<in> set (neighbors m x y). q \<noteq> p \<and> (\<forall>r. in_map r m \<and> r \<noteq> p \<longrightarrow> dist p r \<ge> dist p q \<or> dist p r \<ge> d)"
proof -
  obtain z zs where "set (z # zs) = set (neighbors m x y) - {p}"
    by (metis assms(2) all_not_in_conv insert_absorb list.simps(15) set_removeAll)
  hence "\<exists>q \<in> set (neighbors m x y) - {p}.\<forall> r \<in> set (neighbors m x y)  - {p}. dist p r \<ge> dist p q"
    using dist_compact_on_finite by fast
  then obtain q where "q \<in> set (neighbors m x y) - {p}" "\<forall> r \<in> set (neighbors m x y)  - {p}. dist p r \<ge> dist p q"
    by blast
  then show ?thesis using dist_of_non_neighbors[of p m x y xs d] assms by fastforce
qed 

definition find_in_grid_map :: "int \<Rightarrow> int \<Rightarrow> grid_map \<Rightarrow> real" where 
"find_in_grid_map x y m \<equiv>  brute_force_dist (build_pairs (neighbors m x y))"

lemma find_in_grid_map_pos:
	assumes "p \<in> set (neighbors m x y)" "q \<in> set (neighbors m x y)" "p \<noteq> q"
	shows "find_in_grid_map x y m > 0"
proof -
	have "(p, q) \<in> set (build_pairs (neighbors m x y)) \<or> (q, p) \<in> set (build_pairs (neighbors m x y))" 
		using assms using build_pairs_sound by blast
	hence "build_pairs (neighbors m x y) \<noteq> []" 
		by force
	then show ?thesis 
		unfolding find_in_grid_map_def 
		using brute_force_dist_pos  sorry
qed 

theorem find_in_grid_map_correct:
  fixes p q
  assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "p \<in> set (m x y)" "in_map q m" "q \<noteq> p"
  shows "(dist p q \<ge> find_in_grid_map x y m \<and> find_in_grid_map x y m > 0) \<or> dist p q \<ge> d"
proof (cases "set (neighbors m x y) - {p} \<noteq> {}")
  case True
  then obtain r where r_def: "r \<in> set (neighbors m x y)" "r \<noteq> p" 
      "(\<forall>s. in_map s m \<and> s \<noteq> p \<longrightarrow> dist p r \<le> dist p s \<or>  d \<le> dist p s)"
    using nearest_in_neighbors assms by blast
  from r_def(3) assms(4, 5) have A: "dist p r \<le> dist p q \<or> d \<le> dist p q" by fastforce 
  from assms(3) have B:"p \<in> set (neighbors m x y)"
    unfolding neighbors_def by fastforce
  from this r_def(1) r_def(2) have 
    "(r, p) \<in> set (build_pairs (neighbors m x y)) \<or> (p, r) \<in> set (build_pairs (neighbors m x y))"
    using build_pairs_sound[of r "neighbors m x y" p] by blast
  then consider "(r, p) \<in> set (build_pairs (neighbors m x y))" | "(p, r) \<in> set (build_pairs (neighbors m x y))"
    by blast
  then have C:"find_in_grid_map x y m \<le> dist p r"
    unfolding find_in_grid_map_def
    using dist_symm by (cases; metis brute_force_dist_correct)+
  have "find_in_grid_map x y m > 0"
  	using r_def B find_in_grid_map_pos by blast
  then show ?thesis using A C by linarith
next
  case False
  then show ?thesis using dist_of_non_neighbors[of p m x y xs d "fst q" "snd q"] assms by auto 
qed

lemma find_in_grid_map_exist:
	assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "find_in_grid_map x y m < d" "find_in_grid_map x y m > 0"
	shows "\<exists>p q. p \<in> set (neighbors m x y) \<and> q \<in> set (neighbors m x y) \<and> find_in_grid_map x y m = dist p q"
proof -
	let ?d = "find_in_grid_map x y m"
	let ?n = "neighbors m x y"
	consider "length ?n = 0" | "length ?n = 1" | "length ?n \<ge> 2" 
		by linarith
	then show ?thesis 
	proof cases
		case 1
		then have "?d = -1" 
			unfolding find_in_grid_map_def by simp
		then show ?thesis 
			using assms by linarith
	next
		case 2
		then have "\<exists>a. ?n = [a]" 
			by (auto simp add: length_Suc_conv)
		then obtain a where "?n = [a]" 
			by blast
		then have "?d = -1" 
			unfolding find_in_grid_map_def by simp
		then show ?thesis 
			using assms by linarith
	next
		case 3
		then have "build_pairs (?n) \<noteq> []" 
			using assms(4) find_in_grid_map_def by force
		then have "\<exists>(p, q)\<in>set (build_pairs (?n)). ?d = dist p q"
			unfolding find_in_grid_map_def 
			using brute_force_dist_exists by blast
		then obtain p q where "(p, q) \<in> set (build_pairs (?n))" "?d = dist p q"
			by blast 
		moreover then have "p \<in> set ?n" "q \<in> set ?n"
			using build_pairs_complete by blast+
		ultimately show ?thesis by blast
	qed
qed


section "Introduce Randomization" 

fun traverse_grid_map :: "point list \<Rightarrow> real \<Rightarrow> grid_map \<Rightarrow> real"
	where 
"traverse_grid_map [] d _ = d" | 
"traverse_grid_map (z # zs) d m = (
	let x = \<lfloor>(fst z) / d\<rfloor>; y = \<lfloor>(snd z) / d\<rfloor>; 
	prev =  (traverse_grid_map zs d m); curr = find_in_grid_map x y m in
	if prev \<ge> curr \<and> curr > 0 then curr else prev
)"

lemma traverse_grid_map_pos: 
"d > 0  \<Longrightarrow> traverse_grid_map xs d m > 0"
	by (induction xs) (auto simp: Let_def)


lemma traverse_grid_map_upper:
	assumes "d > 0" "p \<in> set xs" "q \<in> set xs" "p \<noteq> q" "m = build_grid_map xs d (\<lambda>_ _. [])"
	shows "traverse_grid_map xs d m \<le> min d (dist p q)"
proof -
	let ?x1 = "\<lfloor>fst p / d\<rfloor>" let ?y1 = "\<lfloor>snd p / d\<rfloor>"
	let ?x2 = "\<lfloor>fst q / d\<rfloor>" let ?y2 = "\<lfloor>snd q / d\<rfloor>"
	from assms have "p \<in> set (m ?x1 ?y1)" "q \<in> set (m ?x2 ?y2)" 
   	using build_grid_map_sound by blast+ 
  moreover then have "in_map p m" "in_map q m"
		unfolding in_map_def by blast+ 
	ultimately have A: "(dist p q \<ge> find_in_grid_map ?x1 ?y1 m \<and> find_in_grid_map ?x1 ?y1 m > 0) \<or> dist p q \<ge> d" and
									"(dist q p \<ge> find_in_grid_map ?x2 ?y2 m \<and> find_in_grid_map ?x2 ?y2 m > 0) \<or> dist q p \<ge> d"
		using find_in_grid_map_correct assms(1, 4, 5) by auto
	then have B: "(dist p q \<ge> find_in_grid_map ?x2 ?y2 m \<and> find_in_grid_map ?x2 ?y2 m > 0) \<or> dist p q \<ge> d"
		using dist_symm by auto
	from A B assms(1-4) show "traverse_grid_map xs d m \<le> min d (dist p q)"
	proof (induction xs d m rule: traverse_grid_map.induct)
		case (2 z zs d m)
		have C: "traverse_grid_map zs d m \<le> d"
			by (induction zs)  (auto simp: Let_def)
		from 2 consider "p = z" | "q = z" | "p \<in> set zs \<and> q \<in> set zs"
  	by force
 		 then show ?case
		proof cases
			case 1
			then show ?thesis using "local.2.prems" C by (auto simp: Let_def)
		next
			case 2
			then show ?thesis using "local.2.prems" C by (auto simp: Let_def)
		next
			case 3
			with "2" have "traverse_grid_map zs d m \<le> min d (Rabin_Closest_Pair.dist p q)" 
				by blast
			then show ?thesis by (auto simp: Let_def)
		qed
	qed auto
qed 

lemma traverse_grid_map_lower:
	assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "traverse_grid_map xs d m < d" "traverse_grid_map xs d m > 0"
	shows "\<exists>p q. p \<in> set xs \<and> q \<in> set xs \<and> traverse_grid_map xs d m = dist p q"
proof (cases xs)
  case Nil
  then show ?thesis 
  	using assms by simp
next
  let ?d = "traverse_grid_map xs d m"
  case (Cons a list)
	then have "\<exists>r\<in>set xs. ?d = find_in_grid_map  \<lfloor>(fst r) / d\<rfloor>  \<lfloor>(snd r) / d\<rfloor> m"
	using assms(3) proof (induction list arbitrary: a xs)
		case Nil
		then have "traverse_grid_map [a] d m = min (find_in_grid_map \<lfloor>fst a / d\<rfloor> \<lfloor>snd a / d\<rfloor> m) d" 
			by (auto simp: Let_def)
		moreover have "traverse_grid_map [a] d m < d" 
			using Nil by blast
		ultimately show ?case using Nil(1) by force
	next
		case (Cons b bs)
		let ?ys = "b#bs"
		let ?d' = "(find_in_grid_map \<lfloor>fst a / d\<rfloor> \<lfloor>snd a / d\<rfloor> m)"
		let ?d0 = "traverse_grid_map ?ys d m"
		let ?d1 = "traverse_grid_map xs d m"
		have prem: "?d' > 0 \<Longrightarrow>  min ?d' ?d0 = ?d1" 
			by (simp add: Cons(2) Let_def)
		consider "?d' \<le> 0" | "?d' > 0 \<and> ?d0 < d" | "?d' > 0 \<and> ?d0 \<ge> d"
			by argo
		then show ?case 
		proof cases
			case 1
			then have "?d0 = ?d1"
				by (simp add: Cons(2) Let_def)
			then have IH: "\<exists>r\<in>set ?ys. traverse_grid_map ?ys d m = find_in_grid_map \<lfloor>fst r / d\<rfloor> \<lfloor>snd r / d\<rfloor> m"
				using Cons by metis
			then show ?thesis using Cons(2) prem 1 by force 
		next
			case 2
			then have IH: "\<exists>r\<in>set ?ys. traverse_grid_map ?ys d m = find_in_grid_map \<lfloor>fst r / d\<rfloor> \<lfloor>snd r / d\<rfloor> m"
				using Cons by blast
			then show ?thesis using Cons(2) prem 2 by force
		next
			case 3
			then have "?d' < d"
			using Cons(3) prem by linarith
			then have "?d1 = ?d'"
			using prem 3 by linarith
			then show ?thesis using Cons(2) by auto
		qed
	qed
	then obtain r where r_def: "r \<in> set xs" "?d = find_in_grid_map  \<lfloor>(fst r) / d\<rfloor>  \<lfloor>(snd r) / d\<rfloor> m"
		by blast
	let ?x = " \<lfloor>(fst r) / d\<rfloor>" let ?y = "\<lfloor>(snd r) / d\<rfloor>"
	have "\<exists>p q. p \<in> set (neighbors m ?x ?y) \<and> q \<in> set (neighbors m ?x ?y) 
							\<and> find_in_grid_map ?x ?y m = Rabin_Closest_Pair.dist p q"
		using find_in_grid_map_exist assms r_def by simp
	then obtain p q where pq_def: "p \<in> set (neighbors m ?x ?y)" "q \<in> set (neighbors m ?x ?y)"
							"find_in_grid_map ?x ?y m = Rabin_Closest_Pair.dist p q" 
		by blast
	then have "\<exists>x1 y1. p \<in> set (m x1 y1)" "\<exists>x2 y2. q \<in> set (m x2 y2)"
		unfolding neighbors_def by auto
	then have "p \<in> set xs" "q \<in> set xs" 
		using build_grid_map_complete assms(2) by blast+
  then show ?thesis using pq_def(3) r_def(2) by metis
qed

thm find_in_grid_map_exist

(*This shows that our traversal indeed finds the closest pair of points*)

definition closest_dist :: "point list \<Rightarrow> real \<Rightarrow> bool" where 
"closest_dist ps d \<equiv> 
	(\<exists>p q. p \<in> set ps \<and> q \<in> set ps \<and> p \<noteq> q \<and> dist p q = d) \<and>
	(\<forall>p q. p \<in> set ps \<and> q \<in> set ps \<and> p \<noteq> q \<longrightarrow> dist p q \<ge> d)"

lemma closest_dist_gt_zero: "closest_dist ps d \<Longrightarrow> d > 0"
proof -
	assume "closest_dist ps d"
	then obtain p q where pq_def: "p \<noteq> q" "dist p q = d"
		unfolding closest_dist_def by blast
	from pq_def(1) have "(fst p - fst q) \<noteq> 0 \<or> snd p - snd q \<noteq> 0" 
		by (simp add: prod_eq_iff)
	then have "(fst p - fst q)^2 + (snd p - snd q)^2 > 0"
		using sum_power2_gt_zero_iff by blast
	moreover from pq_def(2) have "d = sqrt ((fst p - fst q)^2 + (snd p - snd q)^2)" 
		by (metis dist.simps prod.collapse)
	ultimately show "d > 0" by simp
qed 

definition first_phase :: "point list \<Rightarrow> real pmf" where 
"first_phase ps = do {
	xs \<leftarrow> replicate_pmf (length ps) (pmf_of_set (set (build_pairs ps)));
	return_pmf (brute_force_dist xs)
}"

definition "second_phase ps d \<equiv> (
	let m = build_grid_map ps d (\<lambda>_ _. []) in 
	traverse_grid_map ps d m
)"

definition rabins_closest_pair :: "point list \<Rightarrow> real pmf" where 
"rabins_closest_pair ps = do {
	d \<leftarrow> first_phase ps;
	return_pmf (second_phase ps d)
}"

(*The Las Vegas algorithm outputs the correct distance with probability 1*)
lemma map_replicate_pmf: "map_pmf (map f) (replicate_pmf n p) = replicate_pmf n (map_pmf f p)"
	sorry

lemma first_phase_correct:
	fixes d 
	assumes "distinct ps" "closest_dist ps d" "length ps \<ge> 2" 
	shows "measure (first_phase ps) {x. x \<ge> d} = 1" 
proof -
	let ?ps = "pmf_of_set (set (build_pairs ps))"
	let ?xs = "replicate_pmf (length ps) ?ps"
	have "\<exists>p q qs. ps = p # q # qs" 
		by (metis assms(3) Suc_le_mono length_0_conv length_Cons nle_le numerals(2) remdups_adj.cases zero_order(1))
	then obtain p q qs where "ps = p # q # qs" 
		by blast
	then have prems: "distinct (p # q # qs)" "closest_dist (p # q # qs) d"
		using assms by blast+
	then have "measure (first_phase (p # q # qs)) {x. x \<ge> d} = 1" (is "?L = ?R")
	proof (induction qs arbitrary: p q)
		case Nil
		then have "\<exists>r s. r \<in> set [p, q] \<and> s \<in> set [p, q] \<and> r \<noteq> s \<and> Rabin_Closest_Pair.dist r s = d"
			unfolding closest_dist_def by auto
		then obtain r s where "r \<in> set [p, q]" "s \<in> set [p, q]" "r \<noteq> s" "dist r s = d" 
			by blast
		moreover then have "r = p \<and> s = q \<or> r = q \<and> s = p" 
			by auto
		ultimately have "dist p q = d \<or> dist q p = d" 
			by blast 
		then have "dist p q = d"
			using dist_symm by simp
		have B: "length [p, q] = 2" "set (build_pairs[p, q]) = {(p, q)}" 
			using Nil by auto
		have "measure (first_phase [p, q]) {x. x \<ge> d} = 
							measure (replicate_pmf (length [p, q]) (pmf_of_set (set (build_pairs[p, q])))) {xs . brute_force_dist xs \<ge> d}" 
			by (simp add: first_phase_def map_pmf_def[symmetric])
		also have "... = measure (replicate_pmf 2 (pmf_of_set {(p, q)})) {xs. brute_force_dist xs \<ge> d}"
			by (subst B)+ blast
		then show ?case sorry
	next
		case (Cons a qs)
		then show ?case 
		proof (cases "closest_dist (q # a # qs) d")
			case True
			with Cons have "measure (first_phase (q # a # qs)) {a. d \<le> a} = 1"
				by auto
			then show ?thesis sorry
		next
			case False
			then show ?thesis sorry
		qed
	qed
	then show ?thesis
		using \<open>ps = p # q # qs\<close> by blast
qed 

theorem rabins_closest_pair_correct: 
	fixes d
	assumes "distinct ps" "closest_dist ps d" "length ps \<ge> 2"
	shows "measure (rabins_closest_pair ps) {d} = 1" (is "?L = ?R")
proof -
	let ?d = "first_phase ps"
	have "\<And>x. x \<ge> d \<Longrightarrow> second_phase ps x = d"
	proof -
		fix x
		assume prem: "x \<ge> d"
		have "traverse_grid_map ps x (build_grid_map ps x (\<lambda>_ _. [])) = d" (is "?L = ?R")
		proof -
			let ?m = "build_grid_map ps x (\<lambda>_ _. [])"
			from assms(2) obtain p q where "p \<in> set ps" "q \<in> set ps" "p \<noteq> q" "dist p q = d"
				unfolding closest_dist_def by blast
			moreover have "x > 0" 
				using closest_dist_gt_zero assms(2) prem by force
			ultimately have "?L \<le> min x d" 
				using traverse_grid_map_upper by blast
			also have "... = d" 
				using prem by simp 
			finally have le:"?L \<le> ?R" 
				by blast
			then consider "?L = ?R" | "?L < ?R" 
				by argo
			then show ?thesis
			proof cases
				let ?d = "traverse_grid_map ps x ?m"
				case 2
				then have "?d < x" 
					using prem by argo
				moreover have "?d > 0" 
					using traverse_grid_map_pos \<open>x > 0\<close> by blast
				ultimately  have "\<exists>p q. p \<in> set ps \<and> q \<in> set ps \<and> ?d = dist p q"  
				  using traverse_grid_map_lower by auto
				then obtain p q where pq_def: "p \<in> set ps" "q \<in> set ps" "?d = dist p q" 
					by blast
				moreover then have "p \<noteq> q"
					using dist_pos_rev \<open>?d > 0\<close> by auto
				then have "dist p q \<ge> d"
				  using assms(2) pq_def
				  unfolding closest_dist_def by presburger
				then show ?thesis using 2 pq_def by argo
			qed
		qed
		then show "second_phase ps x = d"
			unfolding second_phase_def Let_def by blast
	qed 
	hence A: "{x. second_phase ps x = d} \<supseteq> {x. x \<ge> d}" 
		by blast
	have "?R = measure ?d {x. x \<ge> d}"
		using first_phase_correct assms by presburger
	also have "... \<le>  measure ?d {x. second_phase ps x = d}"
		by (simp add: A measure_pmf.finite_measure_mono) 
	finally have " measure ?d {x. second_phase ps x = d} = 1"
		by (simp add: measure_pmf.measure_ge_1_iff)
	then show ?thesis 
		by (simp add: rabins_closest_pair_def map_pmf_def[symmetric] vimage_def) 
qed 

find_consts "'a pmf \<Rightarrow> 'a"

end 