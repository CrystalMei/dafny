module ADT {
  export Basic 
    reveals Nat, I0, I1, I2, AbPos, AbIsZero, AbNotNeg
    provides AbInt, I2A, A2D, AbLt, AbAdd, AbSub, AbDiv2, AbDiv, AbLeq, AbLtLt, AbLeqLt,
      /* Properties */
      Props_adt_dt_lt,
      Props_one_in_bound_p2, Props_2is1add1,

      /* Less Than */
      Props_lt_gt_eq_p2, Props_lt_is_not_leq_p2,
      Props_lt2leq_add_p2, Props_lt2leq_sub_p2,
      Props_leq2lt_add_p2, Props_leq2lt_sub_p2,
      Props_lt_addition_p3, Props_lt_subtraction_p3,
      Props_lt_transitive_p3, Props_lt_transitive'_p3,
      Props_lt_add_notneg_p3,

      /* Addition */
      Props_add_commutative_p2, Props_add_associative_p3, Props_add_addition_p3, Props_add_identity_p1,
      Props_add_lt_is_lt_p4, Props_add_notneg_is_leq_p3, Props_add_pos_is_lt_p2, Props_add_pos_is_pos_p2,
      Props_add2sub_p3, Props_sub2add_p3, 
      Props_add_sub_is_add_p3, Props_sub_add_is_sub_p3,
      Props_add_sub_is_orig_p2,

      /* Divide 2 */
      Props_div_pos1_p1, Props_div_pos2_p1, Props_div_zero_p1, Props_div_lt_p1, Props_div_leq_p2, Props_div_add1_leq_p1

  export Ultra
    reveals AbInt, I2A, A2D, AbLt, AbAdd, AbSub, AbDiv2, AbDiv, AbLeq, AbLtLt, AbLeqLt, Nat, I0, I1, I2, AbPos, AbIsZero, AbNotNeg
    provides Props_adt_dt_lt,
      /* Properties */
      Props_one_in_bound_p2, Props_2is1add1,

      /* Less Than */
      Props_lt_gt_eq_p2, Props_lt_is_not_leq_p2,
      Props_lt2leq_add_p2, Props_lt2leq_sub_p2,
      Props_leq2lt_add_p2, Props_leq2lt_sub_p2,
      Props_lt_addition_p3, Props_lt_subtraction_p3,
      Props_lt_transitive_p3, Props_lt_transitive'_p3,
      Props_lt_add_notneg_p3,

      /* Addition */
      Props_add_commutative_p2, Props_add_associative_p3, Props_add_addition_p3, Props_add_identity_p1,
      Props_add_lt_is_lt_p4, Props_add_notneg_is_leq_p3, Props_add_pos_is_lt_p2, Props_add_pos_is_pos_p2,
      Props_add2sub_p3, Props_sub2add_p3, 
      Props_add_sub_is_add_p3, Props_add_sub_is_orig_p2,

      /* Divide 2 */
      Props_div_pos1_p1, Props_div_pos2_p1, Props_div_zero_p1, Props_div_lt_p1, Props_div_leq_p2, Props_div_add1_leq_p1

  type AbInt(!new)(==) = int // (!new): generic type, not a class type
  datatype Nat = Z | S(Nat)
  const I0 : AbInt := I2A(0)
  const I1 : AbInt := I2A(1)
  const I2 : AbInt := I2A(2)

  function method I2A (n: int) : (AbInt) { n }
  function method A2D (a: AbInt) : Nat
  lemma Props_adt_dt_lt (x: AbInt, y: AbInt)
    requires AbLt(x, y)
    ensures A2D(x) < A2D(y)

  predicate AbIsZero (n: AbInt) { n == I0 }
  predicate AbPos (n: AbInt) { AbLt(I0, n) }
  predicate AbNotNeg (n: AbInt) { AbLeq(I0, n) }

  function method AbLt (n: AbInt, m: AbInt) : bool { n < m }
  function method AbAdd (n: AbInt, m: AbInt) : AbInt { n + m }
  function method AbSub (n: AbInt, m: AbInt) : AbInt { n - m }
  function method AbDiv2 (n: AbInt): (r: AbInt)
    ensures AbLeq(AbAdd(r, r), n)
    { n / 2 }
  function method AbDiv (n: AbInt, m: AbInt) : AbInt
    requires m != I0
    { n / m }

  function method AbLeq (n: AbInt, m: AbInt) : (r: bool)
    ensures AbLeq(n, m) <==> AbLt(n, m) || n == m
    { n <= m }
  function method AbLtLt (x: AbInt, l: AbInt, h: AbInt): (r: bool)
    ensures AbLtLt(x, l, h) <==> AbLt(l, x) && AbLt(x, h)
    { l < x && x < h }
  function method AbLeqLt(x: AbInt, l: AbInt, h: AbInt): (r: bool)
    ensures AbLeqLt(x, l, h) <==> AbLeq(l, x) && AbLt(x, h)
    { l <= x < h }

  /* Properties */
  
  lemma Props_2is1add1 ()
    ensures I2 == AbAdd(I1, I1)
    { }
  lemma Props_one_in_bound_p2 (a: AbInt, x: AbInt)
    requires AbLeq(a, x)
    requires AbLt(x, AbAdd(a, I1))
    ensures x == a
    { }

  lemma Props_lt_gt_eq_p2 (x: AbInt, y: AbInt)
    // x < y or x < y or x == y
    ensures AbLt(x, y) || AbLt(y, x) || x == y
    { }
  lemma Props_lt_is_not_leq_p2 (x: AbInt, y: AbInt)
    // x < y or x < y or x == y
    // ensures AbLt(x, y) || AbLt(y, x) || x == y
    ensures AbLt(x, y) <==> !AbLeq(y, x)
    { }
  lemma Props_lt2leq_add_p2 (x: AbInt, y: AbInt)
    // x < y ==> x + 1 <= y
    requires AbLt(x, y)
    ensures AbLeq(AbAdd(x, I1), y)
  lemma Props_lt2leq_sub_p2 (x: AbInt, y: AbInt)
    // x < y ==> x <= y - 1
    requires AbLt(x, y)
    ensures AbLeq(x, AbSub(y, I1))

  lemma Props_leq2lt_sub_p2 (x: AbInt, y: AbInt)
    // x <= y ==> x - 1 < y
    requires AbLeq(x, y)
    ensures AbLt(AbSub(x, I1), y)
  lemma Props_leq2lt_add_p2 (x: AbInt, y: AbInt)
    // x <= y ==> x < y + 1
    requires AbLeq(x, y)
    ensures AbLt(x, AbAdd(y, I1))
    { }

  lemma Props_lt_addition_p3 (x: AbInt, y: AbInt, a: AbInt)
    // x < y ==> x + a < y + a
    requires AbLt(x, y)
    ensures AbLt(AbAdd(x, a), AbAdd(y, a))
    { }
  lemma Props_lt_subtraction_p3 (x: AbInt, y: AbInt, a: AbInt)
    // x < y ==> x - a < y - a
    requires AbLt(x, y)
    ensures AbLt(AbSub(x, a), AbSub(y, a))
    { }
  lemma Props_lt_transitive_p3 (x: AbInt, y: AbInt, z: AbInt)
    // x < y < z
    requires AbLt(x, y)
    requires AbLt(y, z)
    ensures AbLt(x, z)
    { }
  lemma Props_lt_transitive'_p3 (x: AbInt, y: AbInt, z: AbInt)
    // x < y < z
    ensures AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
    { }
  lemma Props_lt_add_notneg_p3 (x: AbInt, y: AbInt, a: AbInt)
    // x + a < y ==> x < y
    requires AbNotNeg(a)
    requires AbLt(AbAdd(x, a), y)
    ensures AbLt(x, y)
    { }

  lemma Props_add_commutative_p2 (x: AbInt, y: AbInt)
    // x + y == y + x
    ensures AbAdd(x, y) == AbAdd(y, x)
    { }
  lemma Props_add_associative_p3 (x: AbInt, y: AbInt, z: AbInt)
    // (x + y) + z == x + (y + z)
    ensures AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
    { }
  lemma Props_add_addition_p3 (x: AbInt, y: AbInt, a: AbInt)
    // x + a == y + a ==> x == y
    ensures AbAdd(x, a) == AbAdd(y, a) <==> x == y
    { }
  lemma Props_add_identity_p1 (x: AbInt)
    // x + 0 == 0 + x == x
    ensures AbAdd(x, I0) == AbAdd(I0, x) == x
    { }

  lemma Props_add_lt_is_lt_p4 (x: AbInt, y: AbInt, a: AbInt, b: AbInt)
    // x = y + a && a < b ==> x < y + b
    requires x == AbAdd(y, a)
    requires AbLt(a, b)
    ensures AbLt(x, AbAdd(y, b))
    { }
  lemma Props_add_notneg_is_leq_p3 (x: AbInt, y: AbInt, a: AbInt)
    //  x + NotNeg == y ==> x <= y
    requires AbNotNeg(a) 
    requires AbAdd(x, a) == y
    ensures AbLeq(x, y)
    { }
  lemma Props_add_pos_is_lt_p2 (x: AbInt, a: AbInt)
    // x < x + Positive (x + Positive != x)
    requires AbPos(a)
    ensures AbLt(x, AbAdd(x, a)); // AbAdd(x, a) != x
    { }
  lemma Props_add_pos_is_pos_p2 (x: AbInt, a: AbInt)
    // NotNeg + Positive is Positive
    requires AbNotNeg(x)
    requires AbPos(a)
    ensures AbPos(AbAdd(x, a))
    { }
  lemma Props_add2sub_p3 (x: AbInt, y: AbInt, z: AbInt)
    // x + y == z ==> x = z - y && y = z - x
    requires AbAdd(x, y) == z
    ensures AbSub(z, x) == y
    { }
  lemma Props_sub2add_p3 (x: AbInt, y: AbInt, z: AbInt)
    // x + y == z ==> x = z - y && y = z - x
    requires AbSub(z, x) == y
    ensures AbAdd(x, y) == z
    { }
  lemma Props_add_sub_is_orig_p2 (x: AbInt, y: AbInt)
    // x + y - y == x
    ensures AbAdd(AbSub(x, y), y) == x
    ensures AbSub(AbAdd(x, y), y) == x
    { }
  lemma Props_add_sub_is_add_p3 (x: AbInt, a: AbInt, b: AbInt)
    // x + b + (a - b) == x + a
    ensures AbAdd(AbAdd(x, b), AbSub(a, b)) == AbAdd(x, a)
    { }
  lemma Props_sub_add_is_sub_p3 (x: AbInt, a: AbInt, b: AbInt)
    // x - (a + b) = x - a - b
    ensures AbSub(x, AbAdd(a, b)) == AbSub(AbSub(x, a), b)
    { }

  lemma Props_div_pos2_p1 (x: AbInt)
    // x / 2 is Positive <==> x >= 2
    requires AbLeq(I2, x) 
    ensures AbPos(AbDiv2(x))
    { }
  lemma Props_div_pos1_p1 (x: AbInt)
    // (x + 1) / 2 is Positive <==> x >= 1
    requires AbLeq(I1, x)
    ensures AbPos(AbDiv2(AbAdd(x, I1)))
    { }
  lemma Props_div_zero_p1 (x: AbInt)
    // 1 / 2 == 0 and 0 / 2 == 0
    requires x == I0 || x == I1
    ensures AbDiv2(x) == I0
    { }
  lemma Props_div_lt_p1 (x: AbInt)
    // I2 <= x ==> x / 2 < x
    requires AbLeq(I2, x)
    ensures AbLt(AbDiv2(x), x)
    { }
  lemma Props_div_leq_p2 (x: AbInt, y: AbInt)
    // y <= x ==> (x + y) / 2 <= x
    requires AbLeq(y, x)
    ensures AbLeq(AbDiv2(AbAdd(x, y)), x)
    { }
  lemma Props_div_add1_leq_p1 (x: AbInt)
    // 1 <= x ==> (x / 2 + 1) <= x
    requires AbLeq(I1, x)
    ensures AbLeq(AbAdd(AbDiv2(x), I1), x)
    { }
}

module ADT_Set {
  import opened ADT`Basic

  function method AbSetLen(s: set<AbInt>) : (l: AbInt)

  // Set generation: lo <= x < hi
  // experiment with more trigger options
  function method AbBoundSet(lo: AbInt, hi: AbInt): (S: set<AbInt>)
    ensures AbSetLen(S) == AbSub(hi, lo)
    ensures forall x :: AbLeq(lo, x) && AbLt(x, hi) <==> x in S
    // Try not to assign every element with AbAdd()
    // ensures S == set x | 0 <= x < len :: AbAdd(lo, int2adt(x))

  lemma Set_Props_len ()
    ensures forall x :: AbLeq(I0, AbSetLen(x))
  
  lemma Set_Props_len_empty ()
    ensures forall x :: AbSetLen(x) == I0 <==> x == {}
  
  lemma Set_Props_len_singlton ()
    ensures forall x: AbInt :: AbSetLen({x}) == I1

  lemma Set_Props_len_element ()
    ensures forall x: AbInt, A: set<AbInt> :: x in A ==> AbSetLen(A) == AbAdd(AbSetLen(A - {x}), I1)

}

import opened ADT`Basic

// Note: Props_notneg () might be an assumption
lemma Props_notneg ()
  ensures forall x :: AbNotNeg(x)

// Note: Props_pos () might be an assumption
lemma Props_pos (x: AbInt)
  ensures AbPos(x)

lemma Props_one_in_bound ()
  ensures forall a, x :: AbLeqLt(x, a, AbAdd(a, I1)) ==> x == a
  { forall a, x | AbLeqLt(x, a, AbAdd(a, I1))
    { Props_one_in_bound_p2(a, x); } }
lemma Props_one_in_bound_x (a: AbInt)
  ensures forall x :: AbLeqLt(x, a, AbAdd(a, I1)) ==> x == a
  { forall x | AbLeqLt(x, a, AbAdd(a, I1))
    { Props_one_in_bound_p2(a, x); } }

lemma Props_lt_gt_eq ()
  // x < y or x < y or x == y
  ensures forall x, y :: AbLt(x, y) || AbLt(y, x) || x == y
  { forall x, y { Props_lt_gt_eq_p2(x, y); } }


lemma Props_lt_props ()
  // x < y or x < y or x == y
  ensures forall x, y :: AbLt(x, y) <==> !(AbLt(y, x) || y == x)
  { forall x, y { Props_lt_is_not_leq_p2(x, y); } }
lemma Props_lt_props_px (x: AbInt)
  // x < y or x < y or x == y
  ensures forall y :: AbLt(x, y) <==> !(AbLt(y, x) || y == x)
  { forall y { Props_lt_is_not_leq_p2(x, y); } }
lemma Props_lt_props_py (y: AbInt)
  // x < y or x < y or x == y
  ensures forall x :: AbLt(x, y) <==> !(AbLt(y, x) || y == x)
  { forall x {Props_lt_is_not_leq_p2(x, y); } }
lemma Props_lt_props_pxy (x: AbInt, y: AbInt)
  // x < y or x < y or x == y
  ensures AbLt(x, y) <==> !(AbLt(y, x) || y == x)
  { Props_lt_is_not_leq_p2(x, y); }

lemma Props_lt_is_not_leq ()
  // x < y or x < y or x == y
  ensures forall x, y :: AbLt(x, y) <==> !AbLeq(y, x)
  ensures forall x, y :: AbLt(x, y) <==> !(AbLt(y, x) || y == x)
  { forall x, y { Props_lt_is_not_leq_p2(x, y); } }

lemma Props_lt_is_not_leq_px (x: AbInt)
  // x < y or x < y or x == y
  ensures forall y :: AbLt(x, y) <==> !AbLeq(y, x)
  ensures forall y :: AbLt(x, y) <==> !(AbLt(y, x) || y == x)
  { forall y { Props_lt_is_not_leq_p2(x, y); } }
lemma Props_lt_is_not_leq_py (y: AbInt)
  // x < y or x < y or x == y
  ensures forall x :: AbLt(x, y) <==> !AbLeq(y, x)
  ensures forall x :: AbLt(x, y) <==> !(AbLt(y, x) || y == x)
  { forall x { Props_lt_is_not_leq_p2(x, y); } }

lemma Props_lt2leq_add ()
  // x < y ==> x + 1 <= y
  ensures forall x, y {:trigger AbLeq(AbAdd(x, I1), y)} :: AbLt(x, y) ==> AbLeq(AbAdd(x, I1), y)
  { forall x, y | AbLt(x, y)
    { Props_lt2leq_add_p2(x, y); } }
lemma Props_lt2leq_sub ()
  // x < y ==> x <= y - 1
  ensures forall x, y {:trigger AbLeq(x, AbSub(y, I1))} :: AbLt(x, y) ==> AbLeq(x, AbSub(y, I1))
  { forall x, y | AbLt(x, y)
    { Props_lt2leq_sub_p2(x, y); } }

lemma Props_lt2leq_add' ()
  // x < y ==> x + 1 <= y
  ensures forall x, y {:trigger AbLt(AbAdd(x, I1), y)} :: AbLt(x, y) ==> AbLt(AbAdd(x, I1), y) || AbAdd(x, I1) == y
  { forall x, y | AbLt(x, y) { Props_lt2leq_add_p2(x, y); } }
lemma Props_lt2leq_sub' ()
  // x < y ==> x <= y - 1
  ensures forall x, y {:trigger AbLt(x, AbSub(y, I1))} :: AbLt(x, y) ==> AbLt(x, AbSub(y, I1)) || x == AbSub(y, I1)
  { forall x, y | AbLt(x, y) { Props_lt2leq_sub_p2(x, y); } }

lemma Props_leq2lt_add ()
  // x <= y ==> x < y + 1
  ensures forall x, y :: AbLeq(x, y) ==> AbLt(x, AbAdd(y, I1))
  { forall x, y | AbLeq(x, y)
    { Props_leq2lt_add_p2(x, y); } }
lemma Props_leq2lt_sub ()
  // x <= y ==> x - 1 < y
  ensures forall x, y :: AbLeq(x, y) ==> AbLt(AbSub(x, I1), y)
  { forall x, y | AbLeq(x, y)
    { Props_leq2lt_sub_p2(x, y); } }

lemma Props_leq2lt_sub' ()
  // x <= y ==> x - 1 < y
  ensures forall x, y {:trigger AbLt(AbSub(x, I1), y)} :: AbLt(x, y) || x == y ==> AbLt(AbSub(x, I1), y)
  { forall x, y | AbLt(x, y) || x == y
    { Props_leq2lt_sub_p2(x, y); } }

lemma Props_lt_addition ()
  // x < y ==> x + a < y + a
  ensures forall x, y, a {:trigger AbAdd(x, a), AbAdd(y, a)}:: AbLt(x, y) ==> AbLt(AbAdd(x, a), AbAdd(y, a))
  { forall x, y, a | AbLt(x, y)
    { Props_lt_addition_p3(x, y, a); } }

lemma Props_lt_subtraction ()
  // x < y ==> x + a < y + a
  ensures forall x, y, a {:trigger AbSub(x, a), AbSub(y, a)} :: AbLt(x, y) ==> AbLt(AbSub(x, a), AbSub(y, a))
  { forall x, y, a | AbLt(x, y)
    { Props_lt_subtraction_p3(x, y, a); } }

lemma Props_lt_transitive ()
  // x < y < z
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall x, y, z | AbLt(x, y) && AbLt(y, z) 
    {Props_lt_transitive_p3(x, y, z); } }
lemma Props_lt_transitive_pyz (y: AbInt, z: AbInt)
  // x < y < z
  ensures forall x :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall x | AbLt(x, y) && AbLt(y, z) 
    {Props_lt_transitive'_p3(x, y, z); } }
lemma Props_lt_transitive' ()
  // x < y < z
  ensures forall x, y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall x, y, z { Props_lt_transitive'_p3(x, y, z); } }
lemma Props_lt_transitive'_px (x: AbInt)
  // x < y < z
  ensures forall y, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall y, z { Props_lt_transitive'_p3(x, y, z); } }
lemma Props_lt_transitive'_py (y: AbInt)
  // x < y < z
  ensures forall x, z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall x, z { Props_lt_transitive'_p3(x, y, z); } }
lemma Props_lt_transitive'_pz (z: AbInt)
  // x < y < z
  ensures forall x, y :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall x, y { Props_lt_transitive'_p3(x, y, z); } }
lemma Props_lt_transitive'_pxy (x: AbInt, y: AbInt)
  // x < y < z
  ensures forall z :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall z { Props_lt_transitive'_p3(x, y, z); } }
lemma Props_lt_transitive'_pxz (x: AbInt, z: AbInt)
  // x < y < z
  ensures forall y :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall y { Props_lt_transitive'_p3(x, y, z); } }
lemma Props_lt_transitive'_pyz (y: AbInt, z: AbInt)
  // x < y < z
  ensures forall x :: AbLt(x, y) && AbLt(y, z) ==> AbLt(x, z)
  { forall x { Props_lt_transitive'_p3(x, y, z); } }

lemma Props_lt_add_notneg ()
  // x + a < y ==> x < y
  ensures forall x, y, a {:trigger AbLt(AbAdd(x, a), y)} :: AbNotNeg(a) && AbLt(AbAdd(x, a), y) ==> AbLt(x, y)
  { forall x, y, a | AbNotNeg(a) && AbLt(AbAdd(x, a), y)
    { Props_lt_add_notneg_p3(x, y, a); } }

lemma Props_add_commutative ()
  // x + y == y + x
  ensures forall x, y :: AbAdd(x, y) == AbAdd(y, x)
  { forall x, y { Props_add_commutative_p2(x, y); } }

lemma Props_add_associative ()
  // (x + y) + z == x + (y + z)
  ensures forall x, y, z :: AbAdd(AbAdd(x, y), z) == AbAdd(x, AbAdd(y, z))
  { forall x, y, z { Props_add_associative_p3(x, y, z); } }

lemma Props_add_addition ()
  // x + a == y + a ==> x == y
  ensures forall x, y, a :: AbAdd(x, a) == AbAdd(y, a) <==> x == y
  { forall x, y, a { Props_add_addition_p3(x, y, a); } }

lemma Props_add_identity ()
  // x + 0 == 0 + x == x
  ensures forall x :: AbAdd(x, I0) == AbAdd(I0, x) == x
  { forall x { Props_add_identity_p1(x); } }

lemma Props_add_lt_is_lt ()
  // x = y + a && a < b ==> x < y + b
  ensures forall x, y, a, b :: x == AbAdd(y, a) && AbLt(a, b) ==> AbLt(x, AbAdd(y, b))
  { forall x, y, a, b | x == AbAdd(y, a) && AbLt(a, b)
    { Props_add_lt_is_lt_p4(x, y, a, b); } }

lemma Props_add_notneg_is_leq ()
  //  x + NotNeg == y ==> x <= y
  ensures forall x, y, a :: AbNotNeg(a) && (AbAdd(x, a) == y) ==> AbLeq(x, y)
  { forall x, y, a | AbNotNeg(a) && (AbAdd(x, a) == y)
    { Props_add_notneg_is_leq_p3(x, y, a); } }

lemma Props_add_pos_is_lt ()
  // x < x + Positive (x + Positive != x)
  ensures forall x, a :: AbPos(a) ==> AbLt(x, AbAdd(x, a)); // AbAdd(x, a) != x
  { forall x, a | AbPos(a)
    { Props_add_pos_is_lt_p2(x, a); } }
  
lemma Props_add_pos_is_pos ()
  // NotNeg + Positive is Positive
  requires forall x :: AbNotNeg(x)
  ensures forall x, a :: AbPos(a) ==> AbPos(AbAdd(x, a))
  { forall x, a | AbPos(a)
    { Props_add_pos_is_pos_p2(x, a); } }

lemma Props_add2sub ()
  // x + y == z ==> x = z - y && y = z - x
  ensures forall x, y, z :: AbAdd(x, y) == z ==> AbSub(z, x) == y
  { forall x, y, z | AbAdd(x, y) == z
    { Props_add2sub_p3(x, y, z); } }
lemma Props_sub2add ()
  // x + y == z ==> x = z - y && y = z - x
  ensures forall x, y, z :: AbSub(z, x) == y ==> AbAdd(x, y) == z
  { forall x, y, z | AbSub(z, x) == y
    { Props_sub2add_p3(x, y, z); } }

lemma Props_add_sub_is_orig ()
  // x + y - y == x
  ensures forall x, y :: AbAdd(AbSub(x, y), y) == x
  ensures forall x, y :: AbSub(AbAdd(x, y), y) == x
  { forall x, y { Props_add_sub_is_orig_p2(x, y); } }

lemma Props_add_sub_is_add ()
  // x + b + (a - b) == x + a
  ensures forall x, a, b :: AbAdd(AbAdd(x, b), AbSub(a, b)) == AbAdd(x, a)
  { forall x, a, b { Props_add_sub_is_add_p3(x, a, b); } }

lemma Props_sub_add_is_sub ()
  // x - (a + b) == x - a - b
  ensures forall x, a, b :: AbSub(x, AbAdd(a, b)) == AbSub(AbSub(x, a), b)
  { forall x, a, b { Props_sub_add_is_sub_p3(x, a, b); } }

lemma Props_div_pos2 ()
  // x / 2 is Positive <==> x >= 2
  ensures forall x :: AbLeq(I2, x) ==> AbPos(AbDiv2(x))
  { forall x | AbLeq(I2, x)
    { Props_div_pos2_p1(x); } }
lemma Props_div_pos1 ()
  // (x + 1) / 2 is Positive <==> x >= 1
  ensures forall x :: AbLeq(I1, x) ==> AbPos(AbDiv2(AbAdd(x, I1)))
  { forall x | AbLeq(I1, x)
    { Props_div_pos1_p1(x); } }
lemma Props_div_zero ()
  // 1 / 2 == 0 and 0 / 2 == 0
  ensures forall x :: x == I0 || x == I1 ==> AbDiv2(x) == I0
  { forall x | x == I0 || x == I1
    { Props_div_zero_p1(x); } }
lemma Props_div_lt ()
  // I2 <= x ==> x / 2 < x
  ensures forall x :: AbLeq(I2, x) ==> AbLt(AbDiv2(x), x)
  { forall x | AbLeq(I2, x)
    { Props_div_lt_p1(x); } }
lemma Props_div_leq ()
  // y <= x ==> (x + y) / 2 <= x
  ensures forall x, y :: AbLeq(y, x) ==> AbLeq(AbDiv2(AbAdd(x, y)), x)
  { forall x, y | AbLeq(y, x)
    { Props_div_leq_p2(x, y); } }
lemma Props_div_add1_leq ()
  // 1 <= x ==> (x / 2 + 1) <= x
  ensures forall x :: AbLeq(I1, x) ==> AbLeq(AbAdd(AbDiv2(x), I1), x)
  { forall x | AbLeq(I1, x)
    { Props_div_add1_leq_p1(x); } }