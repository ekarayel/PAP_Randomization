theory Rabin_Closest_Pair 
  imports "HOL.Real"
begin
  
(* We verify Rabin's closest pair algorithm in 2D Euclidean space *)

section "Preliminaries"

type_synonym point = "real * real"

fun dist :: "point => point => real" where 
"dist (x1, y1) (x2, y2) = (x1 - x2)^2 + (y1 - y2)^2"

fun brute_force_dist :: "(point * point) list => real" where 
"brute_force_dist [] = -1" |
"brute_force_dist (x#xs) = (
    let dist' = brute_force_dist xs; curr = dist (fst x) (snd x) in 
    (if dist' < curr then dist' 
     else curr)
     )"

theorem brute_force_correct: "\<forall>(a, b) \<in> set points. dist a b \<ge> brute_force_dist points"
by (induction points) (auto simp del: dist.simps simp add: Let_def) 

fun build_pairs :: "point list => (point * point) list" where 
"build_pairs [] = []" |
"build_pairs (x#xs) = (map (\<lambda>a. (x, a)) xs) @ build_pairs xs"

lemma build_pairs_correct: " \<forall> a \<in> set xs. \<forall> b \<in> set xs. a \<noteq> b \<longrightarrow> (a, b) \<in> set (build_pairs xs) \<or> (b, a) \<in> set (build_pairs xs)"
by (induction xs) auto

section "Grids"


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
    (\<lambda>z1 z2. if z1 = x \<and> z2 = y then a # (m' z1 z2) else m' z1 z2)
  )"

lemma build_grid_map_sound:
  assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "p \<in> set xs"
  shows "p \<in> set (m \<lfloor>(fst p)/ d\<rfloor>  \<lfloor>(snd p) / d\<rfloor>)"
  using assms apply (induction xs arbitrary: p m)
  by  (auto simp: Let_def; force)+

lemma build_grid_map_complete:
  assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])"
  shows "p \<in> set (m x y) \<Longrightarrow> (x = \<lfloor>(fst p)/ d\<rfloor> \<and> y = \<lfloor>(snd p) / d\<rfloor> \<and> p \<in> set xs)"
using assms proof (induction xs arbitrary: p m x y)
  case (Cons a xs)
  obtain m' where m'_def: "m' = build_grid_map xs d (\<lambda>_ _. [])"
    by blast 
  hence aux1: "m = build_grid_map [a] d m'" 
    by (auto simp: Let_def Cons(4))
  hence aux2: "m x y = a # m' x y \<or> m' x y = m x y" 
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
      case (Cons a list)
      then obtain q where "q \<in> set (m' x y)" 
        by fastforce
      then have "x = \<lfloor>fst q / d\<rfloor> \<and> y = \<lfloor>snd q / d\<rfloor> \<and> q \<in> set xs"
        by (simp add: Cons.IH m'_def assms(1))
      then show ?thesis
        by (smt (verit) Cons.IH Cons.prems(1) assms(1) aux1 build_grid_map.simps(1) 
              build_grid_map.simps(2) list.set_intros(1) list.set_intros(2) m'_def set_ConsD)
    qed
qed simp

thm floor_divide_lower floor_divide_upper

definition find_in_grid_map :: "int \<Rightarrow> int \<Rightarrow> grid_map \<Rightarrow> real" where 
"find_in_grid_map x y m \<equiv>  brute_force_dist (build_pairs (
      m x y @ (m (x + 1) y) @ (m (x - 1) y) @ (m x (y + 1) @ (m x (y - 1)) @ (m (x + 1) (y + 1)) @
      (m (x + 1) (y - 1)) @ (m (x - 1) (y + 1)) @ (m (x - 1) (y - 1))
  )))"


end 