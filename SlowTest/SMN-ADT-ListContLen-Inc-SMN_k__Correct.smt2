(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :smt.CASE_SPLIT 1)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
(set-option :model_compress false)
; done setting options


(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun Ctor (T@T) Int)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun boolType () T@T)
(declare-fun rmodeType () T@T)
(declare-fun stringType () T@T)
(declare-fun regexType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun type (T@U) T@T)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun rmode_2_U (RoundingMode) T@U)
(declare-fun U_2_rmode (T@U) RoundingMode)
(declare-fun string_2_U (String) T@U)
(declare-fun U_2_string (T@U) String)
(declare-fun regex_2_U ((RegEx String)) T@U)
(declare-fun U_2_regex (T@U) (RegEx String))
(declare-fun TyType () T@T)
(declare-fun TBool () T@U)
(declare-fun TChar () T@U)
(declare-fun TInt () T@U)
(declare-fun TReal () T@U)
(declare-fun TORDINAL () T@U)
(declare-fun TyTagType () T@T)
(declare-fun TagBool () T@U)
(declare-fun TagChar () T@U)
(declare-fun TagInt () T@U)
(declare-fun TagReal () T@U)
(declare-fun TagORDINAL () T@U)
(declare-fun TagSet () T@U)
(declare-fun TagISet () T@U)
(declare-fun TagMultiSet () T@U)
(declare-fun TagSeq () T@U)
(declare-fun TagMap () T@U)
(declare-fun TagIMap () T@U)
(declare-fun TagClass () T@U)
(declare-fun ClassNameType () T@T)
(declare-fun class._System.int () T@U)
(declare-fun class._System.bool () T@U)
(declare-fun class._System.set () T@U)
(declare-fun class._System.seq () T@U)
(declare-fun class._System.multiset () T@U)
(declare-fun FieldType (T@T) T@T)
(declare-fun FieldTypeInv0 (T@T) T@T)
(declare-fun alloc () T@U)
(declare-fun NameFamilyType () T@T)
(declare-fun allocName () T@U)
(declare-fun Tagclass._System.nat () T@U)
(declare-fun class._System.object? () T@U)
(declare-fun Tagclass._System.object? () T@U)
(declare-fun Tagclass._System.object () T@U)
(declare-fun class._System.array? () T@U)
(declare-fun Tagclass._System.array? () T@U)
(declare-fun Tagclass._System.array () T@U)
(declare-fun Tagclass._System.___hFunc1 () T@U)
(declare-fun Tagclass._System.___hPartialFunc1 () T@U)
(declare-fun Tagclass._System.___hTotalFunc1 () T@U)
(declare-fun Tagclass._System.___hFunc0 () T@U)
(declare-fun Tagclass._System.___hPartialFunc0 () T@U)
(declare-fun Tagclass._System.___hTotalFunc0 () T@U)
(declare-fun Tagclass._System.___hFunc2 () T@U)
(declare-fun Tagclass._System.___hPartialFunc2 () T@U)
(declare-fun Tagclass._System.___hTotalFunc2 () T@U)
(declare-fun DtCtorIdType () T@T)
(declare-fun |##_System._tuple#2._#Make2| () T@U)
(declare-fun Tagclass._System.Tuple2 () T@U)
(declare-fun class._System.Tuple2 () T@U)
(declare-fun Tagclass._System.___hFunc3 () T@U)
(declare-fun Tagclass._System.___hPartialFunc3 () T@U)
(declare-fun Tagclass._System.___hTotalFunc3 () T@U)
(declare-fun |##_System._tuple#0._#Make0| () T@U)
(declare-fun Tagclass._System.Tuple0 () T@U)
(declare-fun class._System.Tuple0 () T@U)
(declare-fun |##_module.List.Nil| () T@U)
(declare-fun Tagclass._module.List () T@U)
(declare-fun |##_module.List.Cons| () T@U)
(declare-fun class._module.List () T@U)
(declare-fun |##_module.Nat.Z| () T@U)
(declare-fun Tagclass._module.Nat () T@U)
(declare-fun |##_module.Nat.S| () T@U)
(declare-fun class._module.Nat () T@U)
(declare-fun class._module.__default () T@U)
(declare-fun Tagclass._module.__default () T@U)
(declare-fun $$Language$Dafny () Bool)
(declare-fun TBitvector (Int) T@U)
(declare-fun Inv0_TBitvector (T@U) Int)
(declare-fun TSet (T@U) T@U)
(declare-fun Inv0_TSet (T@U) T@U)
(declare-fun TISet (T@U) T@U)
(declare-fun Inv0_TISet (T@U) T@U)
(declare-fun TSeq (T@U) T@U)
(declare-fun Inv0_TSeq (T@U) T@U)
(declare-fun TMultiSet (T@U) T@U)
(declare-fun Inv0_TMultiSet (T@U) T@U)
(declare-fun TMap (T@U T@U) T@U)
(declare-fun Inv0_TMap (T@U) T@U)
(declare-fun Inv1_TMap (T@U) T@U)
(declare-fun TIMap (T@U T@U) T@U)
(declare-fun Inv0_TIMap (T@U) T@U)
(declare-fun Inv1_TIMap (T@U) T@U)
(declare-fun Tag (T@U) T@U)
(declare-fun Lit (T@U) T@U)
(declare-fun BoxType () T@T)
(declare-fun $Box (T@U) T@U)
(declare-fun LitInt (Int) Int)
(declare-fun LitReal (Real) Real)
(declare-fun charType () T@T)
(declare-fun |char#FromInt| (Int) T@U)
(declare-fun |char#ToInt| (T@U) Int)
(declare-fun |char#Plus| (T@U T@U) T@U)
(declare-fun |char#Minus| (T@U T@U) T@U)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun $IsBox (T@U T@U) Bool)
(declare-fun $Is (T@U T@U) Bool)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun MapType0TypeInv0 (T@T) T@T)
(declare-fun MapType0TypeInv1 (T@T) T@T)
(declare-fun MapType0Select (T@U T@U) T@U)
(declare-fun MapType0Store (T@U T@U T@U) T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun SeqTypeInv0 (T@T) T@T)
(declare-fun MapType (T@T T@T) T@T)
(declare-fun MapTypeInv0 (T@T) T@T)
(declare-fun MapTypeInv1 (T@T) T@T)
(declare-fun IMapType (T@T T@T) T@T)
(declare-fun IMapTypeInv0 (T@T) T@T)
(declare-fun IMapTypeInv1 (T@T) T@T)
(declare-fun MapType1Select (T@U T@U) T@U)
(declare-fun MapType1Type () T@T)
(declare-fun MapType1Store (T@U T@U T@U) T@U)
(declare-fun refType () T@T)
(declare-fun $IsAllocBox (T@U T@U T@U) Bool)
(declare-fun $IsAlloc (T@U T@U T@U) Bool)
(declare-fun $IsGoodMultiSet (T@U) Bool)
(declare-fun |Seq#Index| (T@U Int) T@U)
(declare-fun |Seq#Length| (T@U) Int)
(declare-fun |Map#Elements| (T@U) T@U)
(declare-fun |Map#Domain| (T@U) T@U)
(declare-fun |IMap#Elements| (T@U) T@U)
(declare-fun |IMap#Domain| (T@U) T@U)
(declare-fun TypeTuple (T@U T@U) T@U)
(declare-fun TypeTupleCar (T@U) T@U)
(declare-fun TypeTupleCdr (T@U) T@U)
(declare-fun SetRef_to_SetBox (T@U) T@U)
(declare-fun Tclass._System.object? () T@U)
(declare-fun DatatypeTypeType () T@T)
(declare-fun BoxRank (T@U) Int)
(declare-fun DtRank (T@U) Int)
(declare-fun |ORD#Offset| (T@U) Int)
(declare-fun |ORD#FromNat| (Int) T@U)
(declare-fun |ORD#IsNat| (T@U) Bool)
(declare-fun |ORD#Less| (T@U T@U) Bool)
(declare-fun |ORD#LessThanLimit| (T@U T@U) Bool)
(declare-fun |ORD#Plus| (T@U T@U) T@U)
(declare-fun |ORD#Minus| (T@U T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun AtLayer (T@U T@U) T@U)
(declare-fun $LS (T@U) T@U)
(declare-fun IndexField (Int) T@U)
(declare-fun FDim (T@U) Int)
(declare-fun IndexField_Inverse (T@U) Int)
(declare-fun MultiIndexField (T@U Int) T@U)
(declare-fun MultiIndexField_Inverse0 (T@U) T@U)
(declare-fun MultiIndexField_Inverse1 (T@U) Int)
(declare-fun FieldOfDecl (T@T T@U T@U) T@U)
(declare-fun DeclType (T@U) T@U)
(declare-fun DeclName (T@U) T@U)
(declare-fun $HeapSucc (T@U T@U) Bool)
(declare-fun $IsGhostField (T@U) Bool)
(declare-fun _System.array.Length (T@U) Int)
(declare-fun q@Int (Real) Int)
(declare-fun q@Real (Int) Real)
(declare-fun $OneHeap () T@U)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $HeapSuccGhost (T@U T@U) Bool)
(declare-fun |Set#Card| (T@U) Int)
(declare-fun |Set#Empty| (T@T) T@U)
(declare-fun |Set#Singleton| (T@U) T@U)
(declare-fun |Set#UnionOne| (T@U T@U) T@U)
(declare-fun |Set#Union| (T@U T@U) T@U)
(declare-fun |Set#Difference| (T@U T@U) T@U)
(declare-fun |Set#Disjoint| (T@U T@U) Bool)
(declare-fun |Set#Intersection| (T@U T@U) T@U)
(declare-fun |Set#Subset| (T@U T@U) Bool)
(declare-fun |Set#Equal| (T@U T@U) Bool)
(declare-fun |ISet#Empty| (T@T) T@U)
(declare-fun |ISet#UnionOne| (T@U T@U) T@U)
(declare-fun |ISet#Union| (T@U T@U) T@U)
(declare-fun |ISet#Difference| (T@U T@U) T@U)
(declare-fun |ISet#Disjoint| (T@U T@U) Bool)
(declare-fun |ISet#Intersection| (T@U T@U) T@U)
(declare-fun |ISet#Subset| (T@U T@U) Bool)
(declare-fun |ISet#Equal| (T@U T@U) Bool)
(declare-fun |Math#min| (Int Int) Int)
(declare-fun |Math#clip| (Int) Int)
(declare-fun |MultiSet#Card| (T@U) Int)
(declare-fun |MultiSet#Empty| (T@T) T@U)
(declare-fun |MultiSet#Singleton| (T@U) T@U)
(declare-fun |MultiSet#UnionOne| (T@U T@U) T@U)
(declare-fun |MultiSet#Union| (T@U T@U) T@U)
(declare-fun |MultiSet#Intersection| (T@U T@U) T@U)
(declare-fun |MultiSet#Difference| (T@U T@U) T@U)
(declare-fun |MultiSet#Subset| (T@U T@U) Bool)
(declare-fun |MultiSet#Equal| (T@U T@U) Bool)
(declare-fun |MultiSet#Disjoint| (T@U T@U) Bool)
(declare-fun |MultiSet#FromSet| (T@U) T@U)
(declare-fun |MultiSet#FromSeq| (T@U) T@U)
(declare-fun |Seq#Build| (T@U T@U) T@U)
(declare-fun |Seq#Empty| (T@T) T@U)
(declare-fun |Seq#Append| (T@U T@U) T@U)
(declare-fun |Seq#Update| (T@U Int T@U) T@U)
(declare-fun |Seq#Singleton| (T@U) T@U)
(declare-fun |Seq#Build_inv0| (T@U) T@U)
(declare-fun |Seq#Build_inv1| (T@U) T@U)
(declare-fun HandleTypeType () T@T)
(declare-fun |Seq#Create| (T@U T@U Int T@U) T@U)
(declare-fun Apply1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun |Seq#Contains| (T@U T@U) Bool)
(declare-fun |Seq#Take| (T@U Int) T@U)
(declare-fun |Seq#Drop| (T@U Int) T@U)
(declare-fun |Seq#Equal| (T@U T@U) Bool)
(declare-fun |Seq#SameUntil| (T@U T@U Int) Bool)
(declare-fun |Seq#FromArray| (T@U T@U) T@U)
(declare-fun |Seq#Rank| (T@U) Int)
(declare-fun |Map#Card| (T@U) Int)
(declare-fun |Map#Values| (T@U) T@U)
(declare-fun |Map#Items| (T@U) T@U)
(declare-fun _System.Tuple2._0 (T@U) T@U)
(declare-fun _System.Tuple2._1 (T@U) T@U)
(declare-fun |Map#Empty| (T@T T@T) T@U)
(declare-fun |Map#Glue| (T@U T@U T@U) T@U)
(declare-fun |Map#Build| (T@U T@U T@U) T@U)
(declare-fun |Map#Equal| (T@U T@U) Bool)
(declare-fun |Map#Disjoint| (T@U T@U) Bool)
(declare-fun |IMap#Values| (T@U) T@U)
(declare-fun |IMap#Items| (T@U) T@U)
(declare-fun |IMap#Empty| (T@T T@T) T@U)
(declare-fun |IMap#Glue| (T@U T@U T@U) T@U)
(declare-fun |IMap#Build| (T@U T@U T@U) T@U)
(declare-fun |IMap#Equal| (T@U T@U) Bool)
(declare-fun INTERNAL_add_boogie (Int Int) Int)
(declare-fun INTERNAL_sub_boogie (Int Int) Int)
(declare-fun INTERNAL_mul_boogie (Int Int) Int)
(declare-fun INTERNAL_div_boogie (Int Int) Int)
(declare-fun INTERNAL_mod_boogie (Int Int) Int)
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_le_boogie (Int Int) Bool)
(declare-fun INTERNAL_gt_boogie (Int Int) Bool)
(declare-fun INTERNAL_ge_boogie (Int Int) Bool)
(declare-fun Mul (Int Int) Int)
(declare-fun Div (Int Int) Int)
(declare-fun Mod (Int Int) Int)
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Tclass._System.nat () T@U)
(declare-fun null () T@U)
(declare-fun Tclass._System.object () T@U)
(declare-fun Tclass._System.array? (T@U) T@U)
(declare-fun Tclass._System.array?_0 (T@U) T@U)
(declare-fun dtype (T@U) T@U)
(declare-fun Tclass._System.array (T@U) T@U)
(declare-fun Tclass._System.array_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc1_1 (T@U) T@U)
(declare-fun MapType2Type (T@T T@T T@T) T@T)
(declare-fun MapType2TypeInv0 (T@T) T@T)
(declare-fun MapType2TypeInv1 (T@T) T@T)
(declare-fun MapType2TypeInv2 (T@T) T@T)
(declare-fun MapType2Select (T@U T@U T@U) T@U)
(declare-fun MapType2Store (T@U T@U T@U T@U) T@U)
(declare-fun Handle1 (T@U T@U T@U) T@U)
(declare-fun Requires1 (T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0_0 (T@U) T@U)
(declare-fun Apply0 (T@U T@U T@U) T@U)
(declare-fun Handle0 (T@U T@U T@U) T@U)
(declare-fun Requires0 (T@U T@U T@U) Bool)
(declare-fun Reads0 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2_2 (T@U) T@U)
(declare-fun MapType3Type (T@T T@T T@T T@T) T@T)
(declare-fun MapType3TypeInv0 (T@T) T@T)
(declare-fun MapType3TypeInv1 (T@T) T@T)
(declare-fun MapType3TypeInv2 (T@T) T@T)
(declare-fun MapType3TypeInv3 (T@T) T@T)
(declare-fun MapType3Select (T@U T@U T@U T@U) T@U)
(declare-fun MapType3Store (T@U T@U T@U T@U T@U) T@U)
(declare-fun Apply2 (T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Handle2 (T@U T@U T@U) T@U)
(declare-fun Requires2 (T@U T@U T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads2 (T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_2 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_2 (T@U) T@U)
(declare-fun |#_System._tuple#2._#Make2| (T@U T@U) T@U)
(declare-fun DatatypeCtorId (T@U) T@U)
(declare-fun _System.Tuple2.___hMake2_q (T@U) Bool)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
(declare-fun Tclass._System.Tuple2_0 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_1 (T@U) T@U)
(declare-fun |$IsA#_System.Tuple2| (T@U) Bool)
(declare-fun |_System.Tuple2#Equal| (T@U T@U) Bool)
(declare-fun Tclass._System.___hFunc3 (T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc3_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc3_1 (T@U) T@U)
(declare-fun Tclass._System.___hFunc3_2 (T@U) T@U)
(declare-fun Tclass._System.___hFunc3_3 (T@U) T@U)
(declare-fun MapType4Type (T@T T@T T@T T@T T@T) T@T)
(declare-fun MapType4TypeInv0 (T@T) T@T)
(declare-fun MapType4TypeInv1 (T@T) T@T)
(declare-fun MapType4TypeInv2 (T@T) T@T)
(declare-fun MapType4TypeInv3 (T@T) T@T)
(declare-fun MapType4TypeInv4 (T@T) T@T)
(declare-fun MapType4Select (T@U T@U T@U T@U T@U) T@U)
(declare-fun MapType4Store (T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Apply3 (T@U T@U T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Handle3 (T@U T@U T@U) T@U)
(declare-fun Requires3 (T@U T@U T@U T@U T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads3 (T@U T@U T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc3 (T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc3_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc3_1 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc3_2 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc3_3 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc3 (T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc3_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc3_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc3_2 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc3_3 (T@U) T@U)
(declare-fun |#_System._tuple#0._#Make0| () T@U)
(declare-fun _System.Tuple0.___hMake0_q (T@U) Bool)
(declare-fun Tclass._System.Tuple0 () T@U)
(declare-fun |$IsA#_System.Tuple0| (T@U) Bool)
(declare-fun |_System.Tuple0#Equal| (T@U T@U) Bool)
(declare-fun |#_module.List.Nil| () T@U)
(declare-fun _module.List.Nil_q (T@U) Bool)
(declare-fun Tclass._module.List (T@U) T@U)
(declare-fun Tclass._module.List_0 (T@U) T@U)
(declare-fun |#_module.List.Cons| (T@U T@U) T@U)
(declare-fun _module.List.Cons_q (T@U) Bool)
(declare-fun _module.List.head (T@U) T@U)
(declare-fun _module.List.tail (T@U) T@U)
(declare-fun |$IsA#_module.List| (T@U) Bool)
(declare-fun |_module.List#Equal| (T@U T@U) Bool)
(declare-fun |#_module.Nat.Z| () T@U)
(declare-fun _module.Nat.Z_q (T@U) Bool)
(declare-fun Tclass._module.Nat () T@U)
(declare-fun |#_module.Nat.S| (T@U) T@U)
(declare-fun _module.Nat.S_q (T@U) Bool)
(declare-fun _module.Nat._h0 (T@U) T@U)
(declare-fun |$IsA#_module.Nat| (T@U) Bool)
(declare-fun |_module.Nat#Equal| (T@U T@U) Bool)
(declare-fun Tclass._module.__default () T@U)
(declare-fun _module.__default.int2adt (Int) T@U)
(declare-fun |#$AbInt| () T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun |_module.__default.int2adt#canCall| (Int) Bool)
(declare-fun |_module.__default.int2adt#requires| (Int) Bool)
(declare-fun _module.__default.adt2dt (T@U) T@U)
(declare-fun |_module.__default.adt2dt#canCall| (T@U) Bool)
(declare-fun |_module.__default.adt2dt#requires| (T@U) Bool)
(declare-fun _module.__default.AbIsZero (T@U) Bool)
(declare-fun |_module.__default.AbIsZero#canCall| (T@U) Bool)
(declare-fun |_module.__default.AbIsZero#requires| (T@U) Bool)
(declare-fun _module.__default.AbPos (T@U) Bool)
(declare-fun |_module.__default.AbPos#canCall| (T@U) Bool)
(declare-fun |_module.__default.AbPos#requires| (T@U) Bool)
(declare-fun _module.__default.AbLt (T@U T@U) Bool)
(declare-fun |_module.__default.AbLt#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.AbLt#requires| (T@U T@U) Bool)
(declare-fun _module.__default.AbInc1 (T@U) T@U)
(declare-fun |_module.__default.AbInc1#canCall| (T@U) Bool)
(declare-fun |_module.__default.AbInc1#requires| (T@U) Bool)
(declare-fun _module.__default.AbInc (T@U T@U) T@U)
(declare-fun |_module.__default.AbInc#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.AbInc#requires| (T@U T@U) Bool)
(declare-fun _module.__default.AbDec (T@U T@U) T@U)
(declare-fun |_module.__default.AbDec#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.AbDec#requires| (T@U T@U) Bool)
(declare-fun _module.__default.AbDiv2 (T@U) T@U)
(declare-fun |_module.__default.AbDiv2#canCall| (T@U) Bool)
(declare-fun |_module.__default.AbDiv2#requires| (T@U) Bool)
(declare-fun _module.__default.AbSetLen (T@U) T@U)
(declare-fun |_module.__default.AbSetLen#canCall| (T@U) Bool)
(declare-fun |_module.__default.AbSetLen#requires| (T@U) Bool)
(declare-fun _module.__default.AbBoundSet (T@U T@U) T@U)
(declare-fun |_module.__default.AbBoundSet#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.AbBoundSet#requires| (T@U T@U) Bool)
(declare-fun _module.__default.Length (T@U T@U) T@U)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun $LZ () T@U)
(declare-fun |_module.__default.Length#canCall| (T@U) Bool)
(declare-fun |_module.__default.Length#requires| (T@U T@U) Bool)
(declare-fun _module.__default.Split (T@U T@U T@U) T@U)
(declare-fun |_module.__default.Split#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.Split#requires| (T@U T@U T@U) Bool)
(declare-fun _module.__default.Elements (T@U T@U) T@U)
(declare-fun |_module.__default.Elements#canCall| (T@U) Bool)
(declare-fun |_module.__default.Elements#requires| (T@U T@U) Bool)
(declare-fun _module.__default.NoDuplicates (T@U T@U) Bool)
(declare-fun |_module.__default.NoDuplicates#canCall| (T@U) Bool)
(declare-fun |_module.__default.NoDuplicates#requires| (T@U T@U) Bool)
(declare-fun _module.__default.IntRange (T@U T@U) T@U)
(declare-fun |_module.__default.IntRange#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.IntRange#requires| (T@U T@U) Bool)
(declare-fun _module.__default.SmallestMissingNumber (T@U) T@U)
(declare-fun |_module.__default.SmallestMissingNumber#canCall| (T@U) Bool)
(declare-fun |_module.__default.SmallestMissingNumber#requires| (T@U) Bool)
(declare-fun _module.__default.SMN (T@U T@U T@U T@U) T@U)
(declare-fun |_module.__default.SMN#canCall| (T@U T@U T@U) Bool)
(declare-fun |_module.__default.SMN#requires| (T@U T@U T@U T@U) Bool)
(declare-fun _module.__default.SMN_k (T@U T@U T@U T@U) T@U)
(declare-fun |_module.__default.SMN_k#canCall| (T@U T@U T@U) Bool)
(declare-fun |_module.__default.SMN_k#requires| (T@U T@U T@U T@U) Bool)
(declare-fun _module.__default.SMN_k_k (T@U T@U T@U T@U) T@U)
(declare-fun |_module.__default.SMN_k_k#canCall| (T@U T@U T@U) Bool)
(declare-fun |_module.__default.SMN_k_k#requires| (T@U T@U T@U T@U) Bool)
(declare-fun MapType5Type (T@T T@T) T@T)
(declare-fun MapType5TypeInv0 (T@T) T@T)
(declare-fun MapType5TypeInv1 (T@T) T@T)
(declare-fun MapType5Select (T@U T@U T@U) T@U)
(declare-fun MapType5Store (T@U T@U T@U T@U) T@U)
(declare-fun |lambda#0| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#1| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#2| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#3| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#4| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#5| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#6| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#7| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#8| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#9| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#10| (T@U T@U T@U) T@U)
(declare-fun |lambda#11| (T@U T@U T@U) T@U)
(declare-fun |lambda#18| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#21| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#22| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#23| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#24| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#25| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#26| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#27| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#28| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#29| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#30| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#31| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#32| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#33| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#34| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#35| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#36| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#37| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#38| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#39| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#40| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#41| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#42| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#43| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#44| (T@U T@U T@U Bool) T@U)
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (Ctor intType) 0) (= (Ctor realType) 1)) (= (Ctor boolType) 2)) (= (Ctor rmodeType) 3)) (= (Ctor stringType) 4)) (= (Ctor regexType) 5)) (forall ((arg0 Int) ) (! (= (U_2_int (int_2_U arg0)) arg0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0))
))) (forall ((x T@U) ) (!  (=> (= (type x) intType) (= (int_2_U (U_2_int x)) x))
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x))
))) (forall ((arg0@@0 Int) ) (! (= (type (int_2_U arg0@@0)) intType)
 :qid |funType:int_2_U|
 :pattern ( (int_2_U arg0@@0))
))) (forall ((arg0@@1 Real) ) (! (= (U_2_real (real_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_real|
 :pattern ( (real_2_U arg0@@1))
))) (forall ((x@@0 T@U) ) (!  (=> (= (type x@@0) realType) (= (real_2_U (U_2_real x@@0)) x@@0))
 :qid |cast:U_2_real|
 :pattern ( (U_2_real x@@0))
))) (forall ((arg0@@2 Real) ) (! (= (type (real_2_U arg0@@2)) realType)
 :qid |funType:real_2_U|
 :pattern ( (real_2_U arg0@@2))
))) (forall ((arg0@@3 Bool) ) (! (= (U_2_bool (bool_2_U arg0@@3)) arg0@@3)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0@@3))
))) (forall ((x@@1 T@U) ) (!  (=> (= (type x@@1) boolType) (= (bool_2_U (U_2_bool x@@1)) x@@1))
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x@@1))
))) (forall ((arg0@@4 Bool) ) (! (= (type (bool_2_U arg0@@4)) boolType)
 :qid |funType:bool_2_U|
 :pattern ( (bool_2_U arg0@@4))
))) (forall ((arg0@@5 RoundingMode) ) (! (= (U_2_rmode (rmode_2_U arg0@@5)) arg0@@5)
 :qid |typeInv:U_2_rmode|
 :pattern ( (rmode_2_U arg0@@5))
))) (forall ((x@@2 T@U) ) (!  (=> (= (type x@@2) rmodeType) (= (rmode_2_U (U_2_rmode x@@2)) x@@2))
 :qid |cast:U_2_rmode|
 :pattern ( (U_2_rmode x@@2))
))) (forall ((arg0@@6 RoundingMode) ) (! (= (type (rmode_2_U arg0@@6)) rmodeType)
 :qid |funType:rmode_2_U|
 :pattern ( (rmode_2_U arg0@@6))
))) (forall ((arg0@@7 String) ) (! (= (U_2_string (string_2_U arg0@@7)) arg0@@7)
 :qid |typeInv:U_2_string|
 :pattern ( (string_2_U arg0@@7))
))) (forall ((x@@3 T@U) ) (!  (=> (= (type x@@3) stringType) (= (string_2_U (U_2_string x@@3)) x@@3))
 :qid |cast:U_2_string|
 :pattern ( (U_2_string x@@3))
))) (forall ((arg0@@8 String) ) (! (= (type (string_2_U arg0@@8)) stringType)
 :qid |funType:string_2_U|
 :pattern ( (string_2_U arg0@@8))
))) (forall ((arg0@@9 (RegEx String)) ) (! (= (U_2_regex (regex_2_U arg0@@9)) arg0@@9)
 :qid |typeInv:U_2_regex|
 :pattern ( (regex_2_U arg0@@9))
))) (forall ((x@@4 T@U) ) (!  (=> (= (type x@@4) regexType) (= (regex_2_U (U_2_regex x@@4)) x@@4))
 :qid |cast:U_2_regex|
 :pattern ( (U_2_regex x@@4))
))) (forall ((arg0@@10 (RegEx String)) ) (! (= (type (regex_2_U arg0@@10)) regexType)
 :qid |funType:regex_2_U|
 :pattern ( (regex_2_U arg0@@10))
))))
(assert (forall ((x@@5 T@U) ) (! (UOrdering2 x@@5 x@@5)
 :qid |bg:subtype-refl|
 :no-pattern (U_2_int x@@5)
 :no-pattern (U_2_bool x@@5)
)))
(assert (forall ((x@@6 T@U) (y T@U) (z T@U) ) (! (let ((alpha (type x@@6)))
 (=> (and (and (= (type y) alpha) (= (type z) alpha)) (and (UOrdering2 x@@6 y) (UOrdering2 y z))) (UOrdering2 x@@6 z)))
 :qid |bg:subtype-trans|
 :pattern ( (UOrdering2 x@@6 y) (UOrdering2 y z))
)))
(assert (forall ((x@@7 T@U) (y@@0 T@U) ) (! (let ((alpha@@0 (type x@@7)))
 (=> (= (type y@@0) alpha@@0) (=> (and (UOrdering2 x@@7 y@@0) (UOrdering2 y@@0 x@@7)) (= x@@7 y@@0))))
 :qid |bg:subtype-antisymm|
 :pattern ( (UOrdering2 x@@7 y@@0) (UOrdering2 y@@0 x@@7))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (Ctor TyType) 6) (= (type TBool) TyType)) (= (type TChar) TyType)) (= (type TInt) TyType)) (= (type TReal) TyType)) (= (type TORDINAL) TyType)) (= (Ctor TyTagType) 7)) (= (type TagBool) TyTagType)) (= (type TagChar) TyTagType)) (= (type TagInt) TyTagType)) (= (type TagReal) TyTagType)) (= (type TagORDINAL) TyTagType)) (= (type TagSet) TyTagType)) (= (type TagISet) TyTagType)) (= (type TagMultiSet) TyTagType)) (= (type TagSeq) TyTagType)) (= (type TagMap) TyTagType)) (= (type TagIMap) TyTagType)) (= (type TagClass) TyTagType)) (= (Ctor ClassNameType) 8)) (= (type class._System.int) ClassNameType)) (= (type class._System.bool) ClassNameType)) (= (type class._System.set) ClassNameType)) (= (type class._System.seq) ClassNameType)) (= (type class._System.multiset) ClassNameType)) (forall ((arg0@@11 T@T) ) (! (= (Ctor (FieldType arg0@@11)) 9)
 :qid |ctor:FieldType|
))) (forall ((arg0@@12 T@T) ) (! (= (FieldTypeInv0 (FieldType arg0@@12)) arg0@@12)
 :qid |typeInv:FieldTypeInv0|
 :pattern ( (FieldType arg0@@12))
))) (= (type alloc) (FieldType boolType))) (= (Ctor NameFamilyType) 10)) (= (type allocName) NameFamilyType)) (= (type Tagclass._System.nat) TyTagType)) (= (type class._System.object?) ClassNameType)) (= (type Tagclass._System.object?) TyTagType)) (= (type Tagclass._System.object) TyTagType)) (= (type class._System.array?) ClassNameType)) (= (type Tagclass._System.array?) TyTagType)) (= (type Tagclass._System.array) TyTagType)) (= (type Tagclass._System.___hFunc1) TyTagType)) (= (type Tagclass._System.___hPartialFunc1) TyTagType)) (= (type Tagclass._System.___hTotalFunc1) TyTagType)) (= (type Tagclass._System.___hFunc0) TyTagType)) (= (type Tagclass._System.___hPartialFunc0) TyTagType)) (= (type Tagclass._System.___hTotalFunc0) TyTagType)) (= (type Tagclass._System.___hFunc2) TyTagType)) (= (type Tagclass._System.___hPartialFunc2) TyTagType)) (= (type Tagclass._System.___hTotalFunc2) TyTagType)) (= (Ctor DtCtorIdType) 11)) (= (type |##_System._tuple#2._#Make2|) DtCtorIdType)) (= (type Tagclass._System.Tuple2) TyTagType)) (= (type class._System.Tuple2) ClassNameType)) (= (type Tagclass._System.___hFunc3) TyTagType)) (= (type Tagclass._System.___hPartialFunc3) TyTagType)) (= (type Tagclass._System.___hTotalFunc3) TyTagType)) (= (type |##_System._tuple#0._#Make0|) DtCtorIdType)) (= (type Tagclass._System.Tuple0) TyTagType)) (= (type class._System.Tuple0) ClassNameType)) (= (type |##_module.List.Nil|) DtCtorIdType)) (= (type Tagclass._module.List) TyTagType)) (= (type |##_module.List.Cons|) DtCtorIdType)) (= (type class._module.List) ClassNameType)) (= (type |##_module.Nat.Z|) DtCtorIdType)) (= (type Tagclass._module.Nat) TyTagType)) (= (type |##_module.Nat.S|) DtCtorIdType)) (= (type class._module.Nat) ClassNameType)) (= (type class._module.__default) ClassNameType)) (= (type Tagclass._module.__default) TyTagType)))
(assert (distinct TBool TChar TInt TReal TORDINAL TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass class._System.int class._System.bool class._System.set class._System.seq class._System.multiset alloc allocName Tagclass._System.nat class._System.object? Tagclass._System.object? Tagclass._System.object class._System.array? Tagclass._System.array? Tagclass._System.array Tagclass._System.___hFunc1 Tagclass._System.___hPartialFunc1 Tagclass._System.___hTotalFunc1 Tagclass._System.___hFunc0 Tagclass._System.___hPartialFunc0 Tagclass._System.___hTotalFunc0 Tagclass._System.___hFunc2 Tagclass._System.___hPartialFunc2 Tagclass._System.___hTotalFunc2 |##_System._tuple#2._#Make2| Tagclass._System.Tuple2 class._System.Tuple2 Tagclass._System.___hFunc3 Tagclass._System.___hPartialFunc3 Tagclass._System.___hTotalFunc3 |##_System._tuple#0._#Make0| Tagclass._System.Tuple0 class._System.Tuple0 |##_module.List.Nil| Tagclass._module.List |##_module.List.Cons| class._module.List |##_module.Nat.Z| Tagclass._module.Nat |##_module.Nat.S| class._module.Nat class._module.__default Tagclass._module.__default)
)
(assert $$Language$Dafny)
(assert (forall ((arg0@@13 Int) ) (! (= (type (TBitvector arg0@@13)) TyType)
 :qid |funType:TBitvector|
 :pattern ( (TBitvector arg0@@13))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |DafnyPre.32:15|
 :skolemid |316|
 :pattern ( (TBitvector w))
)))
(assert  (and (forall ((arg0@@14 T@U) ) (! (= (type (TSet arg0@@14)) TyType)
 :qid |funType:TSet|
 :pattern ( (TSet arg0@@14))
)) (forall ((arg0@@15 T@U) ) (! (= (type (Inv0_TSet arg0@@15)) TyType)
 :qid |funType:Inv0_TSet|
 :pattern ( (Inv0_TSet arg0@@15))
))))
(assert (forall ((t T@U) ) (!  (=> (= (type t) TyType) (= (Inv0_TSet (TSet t)) t))
 :qid |DafnyPre.34:15|
 :skolemid |317|
 :pattern ( (TSet t))
)))
(assert  (and (forall ((arg0@@16 T@U) ) (! (= (type (TISet arg0@@16)) TyType)
 :qid |funType:TISet|
 :pattern ( (TISet arg0@@16))
)) (forall ((arg0@@17 T@U) ) (! (= (type (Inv0_TISet arg0@@17)) TyType)
 :qid |funType:Inv0_TISet|
 :pattern ( (Inv0_TISet arg0@@17))
))))
(assert (forall ((t@@0 T@U) ) (!  (=> (= (type t@@0) TyType) (= (Inv0_TISet (TISet t@@0)) t@@0))
 :qid |DafnyPre.36:15|
 :skolemid |318|
 :pattern ( (TISet t@@0))
)))
(assert  (and (forall ((arg0@@18 T@U) ) (! (= (type (TSeq arg0@@18)) TyType)
 :qid |funType:TSeq|
 :pattern ( (TSeq arg0@@18))
)) (forall ((arg0@@19 T@U) ) (! (= (type (Inv0_TSeq arg0@@19)) TyType)
 :qid |funType:Inv0_TSeq|
 :pattern ( (Inv0_TSeq arg0@@19))
))))
(assert (forall ((t@@1 T@U) ) (!  (=> (= (type t@@1) TyType) (= (Inv0_TSeq (TSeq t@@1)) t@@1))
 :qid |DafnyPre.38:15|
 :skolemid |319|
 :pattern ( (TSeq t@@1))
)))
(assert  (and (forall ((arg0@@20 T@U) ) (! (= (type (TMultiSet arg0@@20)) TyType)
 :qid |funType:TMultiSet|
 :pattern ( (TMultiSet arg0@@20))
)) (forall ((arg0@@21 T@U) ) (! (= (type (Inv0_TMultiSet arg0@@21)) TyType)
 :qid |funType:Inv0_TMultiSet|
 :pattern ( (Inv0_TMultiSet arg0@@21))
))))
(assert (forall ((t@@2 T@U) ) (!  (=> (= (type t@@2) TyType) (= (Inv0_TMultiSet (TMultiSet t@@2)) t@@2))
 :qid |DafnyPre.40:15|
 :skolemid |320|
 :pattern ( (TMultiSet t@@2))
)))
(assert  (and (forall ((arg0@@22 T@U) (arg1 T@U) ) (! (= (type (TMap arg0@@22 arg1)) TyType)
 :qid |funType:TMap|
 :pattern ( (TMap arg0@@22 arg1))
)) (forall ((arg0@@23 T@U) ) (! (= (type (Inv0_TMap arg0@@23)) TyType)
 :qid |funType:Inv0_TMap|
 :pattern ( (Inv0_TMap arg0@@23))
))))
(assert (forall ((t@@3 T@U) (u T@U) ) (!  (=> (and (= (type t@@3) TyType) (= (type u) TyType)) (= (Inv0_TMap (TMap t@@3 u)) t@@3))
 :qid |DafnyPre.43:15|
 :skolemid |321|
 :pattern ( (TMap t@@3 u))
)))
(assert (forall ((arg0@@24 T@U) ) (! (= (type (Inv1_TMap arg0@@24)) TyType)
 :qid |funType:Inv1_TMap|
 :pattern ( (Inv1_TMap arg0@@24))
)))
(assert (forall ((t@@4 T@U) (u@@0 T@U) ) (!  (=> (and (= (type t@@4) TyType) (= (type u@@0) TyType)) (= (Inv1_TMap (TMap t@@4 u@@0)) u@@0))
 :qid |DafnyPre.44:15|
 :skolemid |322|
 :pattern ( (TMap t@@4 u@@0))
)))
(assert  (and (forall ((arg0@@25 T@U) (arg1@@0 T@U) ) (! (= (type (TIMap arg0@@25 arg1@@0)) TyType)
 :qid |funType:TIMap|
 :pattern ( (TIMap arg0@@25 arg1@@0))
)) (forall ((arg0@@26 T@U) ) (! (= (type (Inv0_TIMap arg0@@26)) TyType)
 :qid |funType:Inv0_TIMap|
 :pattern ( (Inv0_TIMap arg0@@26))
))))
(assert (forall ((t@@5 T@U) (u@@1 T@U) ) (!  (=> (and (= (type t@@5) TyType) (= (type u@@1) TyType)) (= (Inv0_TIMap (TIMap t@@5 u@@1)) t@@5))
 :qid |DafnyPre.47:15|
 :skolemid |323|
 :pattern ( (TIMap t@@5 u@@1))
)))
(assert (forall ((arg0@@27 T@U) ) (! (= (type (Inv1_TIMap arg0@@27)) TyType)
 :qid |funType:Inv1_TIMap|
 :pattern ( (Inv1_TIMap arg0@@27))
)))
(assert (forall ((t@@6 T@U) (u@@2 T@U) ) (!  (=> (and (= (type t@@6) TyType) (= (type u@@2) TyType)) (= (Inv1_TIMap (TIMap t@@6 u@@2)) u@@2))
 :qid |DafnyPre.48:15|
 :skolemid |324|
 :pattern ( (TIMap t@@6 u@@2))
)))
(assert (forall ((arg0@@28 T@U) ) (! (= (type (Tag arg0@@28)) TyTagType)
 :qid |funType:Tag|
 :pattern ( (Tag arg0@@28))
)))
(assert (= (Tag TBool) TagBool))
(assert (= (Tag TChar) TagChar))
(assert (= (Tag TInt) TagInt))
(assert (= (Tag TReal) TagReal))
(assert (= (Tag TORDINAL) TagORDINAL))
(assert (forall ((t@@7 T@U) ) (!  (=> (= (type t@@7) TyType) (= (Tag (TSet t@@7)) TagSet))
 :qid |DafnyPre.74:15|
 :skolemid |325|
 :pattern ( (TSet t@@7))
)))
(assert (forall ((t@@8 T@U) ) (!  (=> (= (type t@@8) TyType) (= (Tag (TISet t@@8)) TagISet))
 :qid |DafnyPre.75:15|
 :skolemid |326|
 :pattern ( (TISet t@@8))
)))
(assert (forall ((t@@9 T@U) ) (!  (=> (= (type t@@9) TyType) (= (Tag (TMultiSet t@@9)) TagMultiSet))
 :qid |DafnyPre.76:15|
 :skolemid |327|
 :pattern ( (TMultiSet t@@9))
)))
(assert (forall ((t@@10 T@U) ) (!  (=> (= (type t@@10) TyType) (= (Tag (TSeq t@@10)) TagSeq))
 :qid |DafnyPre.77:15|
 :skolemid |328|
 :pattern ( (TSeq t@@10))
)))
(assert (forall ((t@@11 T@U) (u@@3 T@U) ) (!  (=> (and (= (type t@@11) TyType) (= (type u@@3) TyType)) (= (Tag (TMap t@@11 u@@3)) TagMap))
 :qid |DafnyPre.78:15|
 :skolemid |329|
 :pattern ( (TMap t@@11 u@@3))
)))
(assert (forall ((t@@12 T@U) (u@@4 T@U) ) (!  (=> (and (= (type t@@12) TyType) (= (type u@@4) TyType)) (= (Tag (TIMap t@@12 u@@4)) TagIMap))
 :qid |DafnyPre.79:15|
 :skolemid |330|
 :pattern ( (TIMap t@@12 u@@4))
)))
(assert (forall ((arg0@@29 T@U) ) (! (let ((T (type arg0@@29)))
(= (type (Lit arg0@@29)) T))
 :qid |funType:Lit|
 :pattern ( (Lit arg0@@29))
)))
(assert (forall ((x@@8 T@U) ) (! (= (Lit x@@8) x@@8)
 :qid |DafnyPre.84:29|
 :skolemid |331|
 :pattern ( (Lit x@@8))
)))
(assert  (and (= (Ctor BoxType) 12) (forall ((arg0@@30 T@U) ) (! (= (type ($Box arg0@@30)) BoxType)
 :qid |funType:$Box|
 :pattern ( ($Box arg0@@30))
))))
(assert (forall ((x@@9 T@U) ) (! (= ($Box (Lit x@@9)) (Lit ($Box x@@9)))
 :qid |DafnyPre.85:18|
 :skolemid |332|
 :pattern ( ($Box (Lit x@@9)))
)))
(assert (forall ((x@@10 Int) ) (! (= (LitInt x@@10) x@@10)
 :qid |DafnyPre.90:29|
 :skolemid |333|
 :pattern ( (LitInt x@@10))
)))
(assert (forall ((x@@11 Int) ) (! (= ($Box (int_2_U (LitInt x@@11))) (Lit ($Box (int_2_U x@@11))))
 :qid |DafnyPre.91:15|
 :skolemid |334|
 :pattern ( ($Box (int_2_U (LitInt x@@11))))
)))
(assert (forall ((x@@12 Real) ) (! (= (LitReal x@@12) x@@12)
 :qid |DafnyPre.92:30|
 :skolemid |335|
 :pattern ( (LitReal x@@12))
)))
(assert (forall ((x@@13 Real) ) (! (= ($Box (real_2_U (LitReal x@@13))) (Lit ($Box (real_2_U x@@13))))
 :qid |DafnyPre.93:15|
 :skolemid |336|
 :pattern ( ($Box (real_2_U (LitReal x@@13))))
)))
(assert  (and (= (Ctor charType) 13) (forall ((arg0@@31 Int) ) (! (= (type (|char#FromInt| arg0@@31)) charType)
 :qid |funType:char#FromInt|
 :pattern ( (|char#FromInt| arg0@@31))
))))
(assert (forall ((ch T@U) ) (!  (=> (= (type ch) charType) (and (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (<= 0 (|char#ToInt| ch))) (< (|char#ToInt| ch) 65536)))
 :qid |DafnyPre.102:15|
 :skolemid |337|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((n Int) ) (!  (=> (and (<= 0 n) (< n 65536)) (= (|char#ToInt| (|char#FromInt| n)) n))
 :qid |DafnyPre.106:15|
 :skolemid |338|
 :pattern ( (|char#FromInt| n))
)))
(assert (forall ((arg0@@32 T@U) (arg1@@1 T@U) ) (! (= (type (|char#Plus| arg0@@32 arg1@@1)) charType)
 :qid |funType:char#Plus|
 :pattern ( (|char#Plus| arg0@@32 arg1@@1))
)))
(assert (forall ((a T@U) (b T@U) ) (!  (=> (and (= (type a) charType) (= (type b) charType)) (= (|char#Plus| a b) (|char#FromInt| (+ (|char#ToInt| a) (|char#ToInt| b)))))
 :qid |DafnyPre.112:15|
 :skolemid |339|
 :pattern ( (|char#Plus| a b))
)))
(assert (forall ((arg0@@33 T@U) (arg1@@2 T@U) ) (! (= (type (|char#Minus| arg0@@33 arg1@@2)) charType)
 :qid |funType:char#Minus|
 :pattern ( (|char#Minus| arg0@@33 arg1@@2))
)))
(assert (forall ((a@@0 T@U) (b@@0 T@U) ) (!  (=> (and (= (type a@@0) charType) (= (type b@@0) charType)) (= (|char#Minus| a@@0 b@@0) (|char#FromInt| (- (|char#ToInt| a@@0) (|char#ToInt| b@@0)))))
 :qid |DafnyPre.115:15|
 :skolemid |340|
 :pattern ( (|char#Minus| a@@0 b@@0))
)))
(assert (forall ((T@@0 T@T) (arg0@@34 T@U) ) (! (= (type ($Unbox T@@0 arg0@@34)) T@@0)
 :qid |funType:$Unbox|
 :pattern ( ($Unbox T@@0 arg0@@34))
)))
(assert (forall ((x@@14 T@U) ) (! (let ((T@@1 (type x@@14)))
(= ($Unbox T@@1 ($Box x@@14)) x@@14))
 :qid |DafnyPre.136:18|
 :skolemid |341|
 :pattern ( ($Box x@@14))
)))
(assert (forall ((bx T@U) ) (!  (=> (and (= (type bx) BoxType) ($IsBox bx TInt)) (and (= ($Box ($Unbox intType bx)) bx) ($Is ($Unbox intType bx) TInt)))
 :qid |DafnyPre.138:15|
 :skolemid |342|
 :pattern ( ($IsBox bx TInt))
)))
(assert (forall ((bx@@0 T@U) ) (!  (=> (and (= (type bx@@0) BoxType) ($IsBox bx@@0 TReal)) (and (= ($Box ($Unbox realType bx@@0)) bx@@0) ($Is ($Unbox realType bx@@0) TReal)))
 :qid |DafnyPre.141:15|
 :skolemid |343|
 :pattern ( ($IsBox bx@@0 TReal))
)))
(assert (forall ((bx@@1 T@U) ) (!  (=> (and (= (type bx@@1) BoxType) ($IsBox bx@@1 TBool)) (and (= ($Box ($Unbox boolType bx@@1)) bx@@1) ($Is ($Unbox boolType bx@@1) TBool)))
 :qid |DafnyPre.144:15|
 :skolemid |344|
 :pattern ( ($IsBox bx@@1 TBool))
)))
(assert (forall ((bx@@2 T@U) ) (!  (=> (and (= (type bx@@2) BoxType) ($IsBox bx@@2 TChar)) (and (= ($Box ($Unbox charType bx@@2)) bx@@2) ($Is ($Unbox charType bx@@2) TChar)))
 :qid |DafnyPre.147:15|
 :skolemid |345|
 :pattern ( ($IsBox bx@@2 TChar))
)))
(assert  (and (and (and (and (and (and (forall ((arg0@@35 T@T) (arg1@@3 T@T) ) (! (= (Ctor (MapType0Type arg0@@35 arg1@@3)) 14)
 :qid |ctor:MapType0Type|
)) (forall ((arg0@@36 T@T) (arg1@@4 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@36 arg1@@4)) arg0@@36)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@36 arg1@@4))
))) (forall ((arg0@@37 T@T) (arg1@@5 T@T) ) (! (= (MapType0TypeInv1 (MapType0Type arg0@@37 arg1@@5)) arg1@@5)
 :qid |typeInv:MapType0TypeInv1|
 :pattern ( (MapType0Type arg0@@37 arg1@@5))
))) (forall ((arg0@@38 T@U) (arg1@@6 T@U) ) (! (let ((aVar1 (MapType0TypeInv1 (type arg0@@38))))
(= (type (MapType0Select arg0@@38 arg1@@6)) aVar1))
 :qid |funType:MapType0Select|
 :pattern ( (MapType0Select arg0@@38 arg1@@6))
))) (forall ((arg0@@39 T@U) (arg1@@7 T@U) (arg2 T@U) ) (! (let ((aVar1@@0 (type arg2)))
(let ((aVar0 (type arg1@@7)))
(= (type (MapType0Store arg0@@39 arg1@@7 arg2)) (MapType0Type aVar0 aVar1@@0))))
 :qid |funType:MapType0Store|
 :pattern ( (MapType0Store arg0@@39 arg1@@7 arg2))
))) (forall ((m T@U) (x0 T@U) (val T@U) ) (! (let ((aVar1@@1 (MapType0TypeInv1 (type m))))
 (=> (= (type val) aVar1@@1) (= (MapType0Select (MapType0Store m x0 val) x0) val)))
 :qid |mapAx0:MapType0Select|
 :weight 0
))) (and (forall ((val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (y0 T@U) ) (!  (or (= x0@@0 y0) (= (MapType0Select (MapType0Store m@@0 x0@@0 val@@0) y0) (MapType0Select m@@0 y0)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
)) (forall ((val@@1 T@U) (m@@1 T@U) (x0@@1 T@U) (y0@@0 T@U) ) (!  (or true (= (MapType0Select (MapType0Store m@@1 x0@@1 val@@1) y0@@0) (MapType0Select m@@1 y0@@0)))
 :qid |mapAx2:MapType0Select|
 :weight 0
)))))
(assert (forall ((bx@@3 T@U) (t@@13 T@U) ) (!  (=> (and (and (= (type bx@@3) BoxType) (= (type t@@13) TyType)) ($IsBox bx@@3 (TSet t@@13))) (and (= ($Box ($Unbox (MapType0Type BoxType boolType) bx@@3)) bx@@3) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@3) (TSet t@@13))))
 :qid |DafnyPre.150:15|
 :skolemid |346|
 :pattern ( ($IsBox bx@@3 (TSet t@@13)))
)))
(assert (forall ((bx@@4 T@U) (t@@14 T@U) ) (!  (=> (and (and (= (type bx@@4) BoxType) (= (type t@@14) TyType)) ($IsBox bx@@4 (TISet t@@14))) (and (= ($Box ($Unbox (MapType0Type BoxType boolType) bx@@4)) bx@@4) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@4) (TISet t@@14))))
 :qid |DafnyPre.153:15|
 :skolemid |347|
 :pattern ( ($IsBox bx@@4 (TISet t@@14)))
)))
(assert (forall ((bx@@5 T@U) (t@@15 T@U) ) (!  (=> (and (and (= (type bx@@5) BoxType) (= (type t@@15) TyType)) ($IsBox bx@@5 (TMultiSet t@@15))) (and (= ($Box ($Unbox (MapType0Type BoxType intType) bx@@5)) bx@@5) ($Is ($Unbox (MapType0Type BoxType intType) bx@@5) (TMultiSet t@@15))))
 :qid |DafnyPre.156:15|
 :skolemid |348|
 :pattern ( ($IsBox bx@@5 (TMultiSet t@@15)))
)))
(assert  (and (forall ((arg0@@40 T@T) ) (! (= (Ctor (SeqType arg0@@40)) 15)
 :qid |ctor:SeqType|
)) (forall ((arg0@@41 T@T) ) (! (= (SeqTypeInv0 (SeqType arg0@@41)) arg0@@41)
 :qid |typeInv:SeqTypeInv0|
 :pattern ( (SeqType arg0@@41))
))))
(assert (forall ((bx@@6 T@U) (t@@16 T@U) ) (!  (=> (and (and (= (type bx@@6) BoxType) (= (type t@@16) TyType)) ($IsBox bx@@6 (TSeq t@@16))) (and (= ($Box ($Unbox (SeqType BoxType) bx@@6)) bx@@6) ($Is ($Unbox (SeqType BoxType) bx@@6) (TSeq t@@16))))
 :qid |DafnyPre.159:15|
 :skolemid |349|
 :pattern ( ($IsBox bx@@6 (TSeq t@@16)))
)))
(assert  (and (and (forall ((arg0@@42 T@T) (arg1@@8 T@T) ) (! (= (Ctor (MapType arg0@@42 arg1@@8)) 16)
 :qid |ctor:MapType|
)) (forall ((arg0@@43 T@T) (arg1@@9 T@T) ) (! (= (MapTypeInv0 (MapType arg0@@43 arg1@@9)) arg0@@43)
 :qid |typeInv:MapTypeInv0|
 :pattern ( (MapType arg0@@43 arg1@@9))
))) (forall ((arg0@@44 T@T) (arg1@@10 T@T) ) (! (= (MapTypeInv1 (MapType arg0@@44 arg1@@10)) arg1@@10)
 :qid |typeInv:MapTypeInv1|
 :pattern ( (MapType arg0@@44 arg1@@10))
))))
(assert (forall ((bx@@7 T@U) (s T@U) (t@@17 T@U) ) (!  (=> (and (and (and (= (type bx@@7) BoxType) (= (type s) TyType)) (= (type t@@17) TyType)) ($IsBox bx@@7 (TMap s t@@17))) (and (= ($Box ($Unbox (MapType BoxType BoxType) bx@@7)) bx@@7) ($Is ($Unbox (MapType BoxType BoxType) bx@@7) (TMap s t@@17))))
 :qid |DafnyPre.162:15|
 :skolemid |350|
 :pattern ( ($IsBox bx@@7 (TMap s t@@17)))
)))
(assert  (and (and (forall ((arg0@@45 T@T) (arg1@@11 T@T) ) (! (= (Ctor (IMapType arg0@@45 arg1@@11)) 17)
 :qid |ctor:IMapType|
)) (forall ((arg0@@46 T@T) (arg1@@12 T@T) ) (! (= (IMapTypeInv0 (IMapType arg0@@46 arg1@@12)) arg0@@46)
 :qid |typeInv:IMapTypeInv0|
 :pattern ( (IMapType arg0@@46 arg1@@12))
))) (forall ((arg0@@47 T@T) (arg1@@13 T@T) ) (! (= (IMapTypeInv1 (IMapType arg0@@47 arg1@@13)) arg1@@13)
 :qid |typeInv:IMapTypeInv1|
 :pattern ( (IMapType arg0@@47 arg1@@13))
))))
(assert (forall ((bx@@8 T@U) (s@@0 T@U) (t@@18 T@U) ) (!  (=> (and (and (and (= (type bx@@8) BoxType) (= (type s@@0) TyType)) (= (type t@@18) TyType)) ($IsBox bx@@8 (TIMap s@@0 t@@18))) (and (= ($Box ($Unbox (IMapType BoxType BoxType) bx@@8)) bx@@8) ($Is ($Unbox (IMapType BoxType BoxType) bx@@8) (TIMap s@@0 t@@18))))
 :qid |DafnyPre.165:15|
 :skolemid |351|
 :pattern ( ($IsBox bx@@8 (TIMap s@@0 t@@18)))
)))
(assert (forall ((v T@U) (t@@19 T@U) ) (!  (=> (= (type t@@19) TyType) (and (=> ($IsBox ($Box v) t@@19) ($Is v t@@19)) (=> ($Is v t@@19) ($IsBox ($Box v) t@@19))))
 :qid |DafnyPre.169:18|
 :skolemid |352|
 :pattern ( ($IsBox ($Box v) t@@19))
)))
(assert  (and (and (and (and (and (forall ((arg0@@48 T@U) (arg1@@14 T@U) ) (! (let ((alpha@@1 (FieldTypeInv0 (type arg1@@14))))
(= (type (MapType1Select arg0@@48 arg1@@14)) alpha@@1))
 :qid |funType:MapType1Select|
 :pattern ( (MapType1Select arg0@@48 arg1@@14))
)) (= (Ctor MapType1Type) 18)) (forall ((arg0@@49 T@U) (arg1@@15 T@U) (arg2@@0 T@U) ) (! (= (type (MapType1Store arg0@@49 arg1@@15 arg2@@0)) MapType1Type)
 :qid |funType:MapType1Store|
 :pattern ( (MapType1Store arg0@@49 arg1@@15 arg2@@0))
))) (forall ((m@@2 T@U) (x0@@2 T@U) (val@@2 T@U) ) (! (let ((alpha@@2 (FieldTypeInv0 (type x0@@2))))
 (=> (= (type val@@2) alpha@@2) (= (MapType1Select (MapType1Store m@@2 x0@@2 val@@2) x0@@2) val@@2)))
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (forall ((val@@3 T@U) (m@@3 T@U) (x0@@3 T@U) (y0@@1 T@U) ) (!  (or (= x0@@3 y0@@1) (= (MapType1Select (MapType1Store m@@3 x0@@3 val@@3) y0@@1) (MapType1Select m@@3 y0@@1)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((val@@4 T@U) (m@@4 T@U) (x0@@4 T@U) (y0@@2 T@U) ) (!  (or true (= (MapType1Select (MapType1Store m@@4 x0@@4 val@@4) y0@@2) (MapType1Select m@@4 y0@@2)))
 :qid |mapAx2:MapType1Select|
 :weight 0
)))) (= (Ctor refType) 19)))
(assert (forall ((v@@0 T@U) (t@@20 T@U) (h T@U) ) (!  (=> (and (= (type t@@20) TyType) (= (type h) (MapType0Type refType MapType1Type))) (and (=> ($IsAllocBox ($Box v@@0) t@@20 h) ($IsAlloc v@@0 t@@20 h)) (=> ($IsAlloc v@@0 t@@20 h) ($IsAllocBox ($Box v@@0) t@@20 h))))
 :qid |DafnyPre.172:18|
 :skolemid |353|
 :pattern ( ($IsAllocBox ($Box v@@0) t@@20 h))
)))
(assert (forall ((v@@1 T@U) ) (!  (=> (= (type v@@1) intType) ($Is v@@1 TInt))
 :qid |DafnyPre.190:14|
 :skolemid |354|
 :pattern ( ($Is v@@1 TInt))
)))
(assert (forall ((v@@2 T@U) ) (!  (=> (= (type v@@2) realType) ($Is v@@2 TReal))
 :qid |DafnyPre.191:14|
 :skolemid |355|
 :pattern ( ($Is v@@2 TReal))
)))
(assert (forall ((v@@3 T@U) ) (!  (=> (= (type v@@3) boolType) ($Is v@@3 TBool))
 :qid |DafnyPre.192:14|
 :skolemid |356|
 :pattern ( ($Is v@@3 TBool))
)))
(assert (forall ((v@@4 T@U) ) (!  (=> (= (type v@@4) charType) ($Is v@@4 TChar))
 :qid |DafnyPre.193:14|
 :skolemid |357|
 :pattern ( ($Is v@@4 TChar))
)))
(assert (forall ((v@@5 T@U) ) (!  (=> (= (type v@@5) BoxType) ($Is v@@5 TORDINAL))
 :qid |DafnyPre.194:14|
 :skolemid |358|
 :pattern ( ($Is v@@5 TORDINAL))
)))
(assert (forall ((h@@0 T@U) (v@@6 T@U) ) (!  (=> (and (= (type h@@0) (MapType0Type refType MapType1Type)) (= (type v@@6) intType)) ($IsAlloc v@@6 TInt h@@0))
 :qid |DafnyPre.196:14|
 :skolemid |359|
 :pattern ( ($IsAlloc v@@6 TInt h@@0))
)))
(assert (forall ((h@@1 T@U) (v@@7 T@U) ) (!  (=> (and (= (type h@@1) (MapType0Type refType MapType1Type)) (= (type v@@7) realType)) ($IsAlloc v@@7 TReal h@@1))
 :qid |DafnyPre.197:14|
 :skolemid |360|
 :pattern ( ($IsAlloc v@@7 TReal h@@1))
)))
(assert (forall ((h@@2 T@U) (v@@8 T@U) ) (!  (=> (and (= (type h@@2) (MapType0Type refType MapType1Type)) (= (type v@@8) boolType)) ($IsAlloc v@@8 TBool h@@2))
 :qid |DafnyPre.198:14|
 :skolemid |361|
 :pattern ( ($IsAlloc v@@8 TBool h@@2))
)))
(assert (forall ((h@@3 T@U) (v@@9 T@U) ) (!  (=> (and (= (type h@@3) (MapType0Type refType MapType1Type)) (= (type v@@9) charType)) ($IsAlloc v@@9 TChar h@@3))
 :qid |DafnyPre.199:14|
 :skolemid |362|
 :pattern ( ($IsAlloc v@@9 TChar h@@3))
)))
(assert (forall ((h@@4 T@U) (v@@10 T@U) ) (!  (=> (and (= (type h@@4) (MapType0Type refType MapType1Type)) (= (type v@@10) BoxType)) ($IsAlloc v@@10 TORDINAL h@@4))
 :qid |DafnyPre.200:14|
 :skolemid |363|
 :pattern ( ($IsAlloc v@@10 TORDINAL h@@4))
)))
(assert (forall ((v@@11 T@U) (t0 T@U) ) (!  (=> (and (= (type v@@11) (MapType0Type BoxType boolType)) (= (type t0) TyType)) (and (=> ($Is v@@11 (TSet t0)) (forall ((bx@@9 T@U) ) (!  (=> (and (= (type bx@@9) BoxType) (U_2_bool (MapType0Select v@@11 bx@@9))) ($IsBox bx@@9 t0))
 :qid |DafnyPre.204:11|
 :skolemid |364|
 :pattern ( (MapType0Select v@@11 bx@@9))
))) (=> (forall ((bx@@10 T@U) ) (!  (=> (and (= (type bx@@10) BoxType) (U_2_bool (MapType0Select v@@11 bx@@10))) ($IsBox bx@@10 t0))
 :qid |DafnyPre.204:11|
 :skolemid |364|
 :pattern ( (MapType0Select v@@11 bx@@10))
)) ($Is v@@11 (TSet t0)))))
 :qid |DafnyPre.202:15|
 :skolemid |365|
 :pattern ( ($Is v@@11 (TSet t0)))
)))
(assert (forall ((v@@12 T@U) (t0@@0 T@U) ) (!  (=> (and (= (type v@@12) (MapType0Type BoxType boolType)) (= (type t0@@0) TyType)) (and (=> ($Is v@@12 (TISet t0@@0)) (forall ((bx@@11 T@U) ) (!  (=> (and (= (type bx@@11) BoxType) (U_2_bool (MapType0Select v@@12 bx@@11))) ($IsBox bx@@11 t0@@0))
 :qid |DafnyPre.208:11|
 :skolemid |366|
 :pattern ( (MapType0Select v@@12 bx@@11))
))) (=> (forall ((bx@@12 T@U) ) (!  (=> (and (= (type bx@@12) BoxType) (U_2_bool (MapType0Select v@@12 bx@@12))) ($IsBox bx@@12 t0@@0))
 :qid |DafnyPre.208:11|
 :skolemid |366|
 :pattern ( (MapType0Select v@@12 bx@@12))
)) ($Is v@@12 (TISet t0@@0)))))
 :qid |DafnyPre.206:15|
 :skolemid |367|
 :pattern ( ($Is v@@12 (TISet t0@@0)))
)))
(assert (forall ((v@@13 T@U) (t0@@1 T@U) ) (!  (=> (and (= (type v@@13) (MapType0Type BoxType intType)) (= (type t0@@1) TyType)) (and (=> ($Is v@@13 (TMultiSet t0@@1)) (forall ((bx@@13 T@U) ) (!  (=> (and (= (type bx@@13) BoxType) (< 0 (U_2_int (MapType0Select v@@13 bx@@13)))) ($IsBox bx@@13 t0@@1))
 :qid |DafnyPre.212:11|
 :skolemid |368|
 :pattern ( (MapType0Select v@@13 bx@@13))
))) (=> (forall ((bx@@14 T@U) ) (!  (=> (and (= (type bx@@14) BoxType) (< 0 (U_2_int (MapType0Select v@@13 bx@@14)))) ($IsBox bx@@14 t0@@1))
 :qid |DafnyPre.212:11|
 :skolemid |368|
 :pattern ( (MapType0Select v@@13 bx@@14))
)) ($Is v@@13 (TMultiSet t0@@1)))))
 :qid |DafnyPre.210:15|
 :skolemid |369|
 :pattern ( ($Is v@@13 (TMultiSet t0@@1)))
)))
(assert (forall ((v@@14 T@U) (t0@@2 T@U) ) (!  (=> (and (and (= (type v@@14) (MapType0Type BoxType intType)) (= (type t0@@2) TyType)) ($Is v@@14 (TMultiSet t0@@2))) ($IsGoodMultiSet v@@14))
 :qid |DafnyPre.214:15|
 :skolemid |370|
 :pattern ( ($Is v@@14 (TMultiSet t0@@2)))
)))
(assert (forall ((arg0@@50 T@U) (arg1@@16 Int) ) (! (let ((T@@2 (SeqTypeInv0 (type arg0@@50))))
(= (type (|Seq#Index| arg0@@50 arg1@@16)) T@@2))
 :qid |funType:Seq#Index|
 :pattern ( (|Seq#Index| arg0@@50 arg1@@16))
)))
(assert (forall ((v@@15 T@U) (t0@@3 T@U) ) (!  (=> (and (= (type v@@15) (SeqType BoxType)) (= (type t0@@3) TyType)) (and (=> ($Is v@@15 (TSeq t0@@3)) (forall ((i Int) ) (!  (=> (and (<= 0 i) (< i (|Seq#Length| v@@15))) ($IsBox (|Seq#Index| v@@15 i) t0@@3))
 :qid |DafnyPre.218:11|
 :skolemid |371|
 :pattern ( (|Seq#Index| v@@15 i))
))) (=> (forall ((i@@0 Int) ) (!  (=> (and (<= 0 i@@0) (< i@@0 (|Seq#Length| v@@15))) ($IsBox (|Seq#Index| v@@15 i@@0) t0@@3))
 :qid |DafnyPre.218:11|
 :skolemid |371|
 :pattern ( (|Seq#Index| v@@15 i@@0))
)) ($Is v@@15 (TSeq t0@@3)))))
 :qid |DafnyPre.216:15|
 :skolemid |372|
 :pattern ( ($Is v@@15 (TSeq t0@@3)))
)))
(assert (forall ((v@@16 T@U) (t0@@4 T@U) (h@@5 T@U) ) (!  (=> (and (and (= (type v@@16) (MapType0Type BoxType boolType)) (= (type t0@@4) TyType)) (= (type h@@5) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@16 (TSet t0@@4) h@@5) (forall ((bx@@15 T@U) ) (!  (=> (and (= (type bx@@15) BoxType) (U_2_bool (MapType0Select v@@16 bx@@15))) ($IsAllocBox bx@@15 t0@@4 h@@5))
 :qid |DafnyPre.223:11|
 :skolemid |373|
 :pattern ( (MapType0Select v@@16 bx@@15))
))) (=> (forall ((bx@@16 T@U) ) (!  (=> (and (= (type bx@@16) BoxType) (U_2_bool (MapType0Select v@@16 bx@@16))) ($IsAllocBox bx@@16 t0@@4 h@@5))
 :qid |DafnyPre.223:11|
 :skolemid |373|
 :pattern ( (MapType0Select v@@16 bx@@16))
)) ($IsAlloc v@@16 (TSet t0@@4) h@@5))))
 :qid |DafnyPre.221:15|
 :skolemid |374|
 :pattern ( ($IsAlloc v@@16 (TSet t0@@4) h@@5))
)))
(assert (forall ((v@@17 T@U) (t0@@5 T@U) (h@@6 T@U) ) (!  (=> (and (and (= (type v@@17) (MapType0Type BoxType boolType)) (= (type t0@@5) TyType)) (= (type h@@6) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@17 (TISet t0@@5) h@@6) (forall ((bx@@17 T@U) ) (!  (=> (and (= (type bx@@17) BoxType) (U_2_bool (MapType0Select v@@17 bx@@17))) ($IsAllocBox bx@@17 t0@@5 h@@6))
 :qid |DafnyPre.227:11|
 :skolemid |375|
 :pattern ( (MapType0Select v@@17 bx@@17))
))) (=> (forall ((bx@@18 T@U) ) (!  (=> (and (= (type bx@@18) BoxType) (U_2_bool (MapType0Select v@@17 bx@@18))) ($IsAllocBox bx@@18 t0@@5 h@@6))
 :qid |DafnyPre.227:11|
 :skolemid |375|
 :pattern ( (MapType0Select v@@17 bx@@18))
)) ($IsAlloc v@@17 (TISet t0@@5) h@@6))))
 :qid |DafnyPre.225:15|
 :skolemid |376|
 :pattern ( ($IsAlloc v@@17 (TISet t0@@5) h@@6))
)))
(assert (forall ((v@@18 T@U) (t0@@6 T@U) (h@@7 T@U) ) (!  (=> (and (and (= (type v@@18) (MapType0Type BoxType intType)) (= (type t0@@6) TyType)) (= (type h@@7) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7) (forall ((bx@@19 T@U) ) (!  (=> (and (= (type bx@@19) BoxType) (< 0 (U_2_int (MapType0Select v@@18 bx@@19)))) ($IsAllocBox bx@@19 t0@@6 h@@7))
 :qid |DafnyPre.231:11|
 :skolemid |377|
 :pattern ( (MapType0Select v@@18 bx@@19))
))) (=> (forall ((bx@@20 T@U) ) (!  (=> (and (= (type bx@@20) BoxType) (< 0 (U_2_int (MapType0Select v@@18 bx@@20)))) ($IsAllocBox bx@@20 t0@@6 h@@7))
 :qid |DafnyPre.231:11|
 :skolemid |377|
 :pattern ( (MapType0Select v@@18 bx@@20))
)) ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7))))
 :qid |DafnyPre.229:15|
 :skolemid |378|
 :pattern ( ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7))
)))
(assert (forall ((v@@19 T@U) (t0@@7 T@U) (h@@8 T@U) ) (!  (=> (and (and (= (type v@@19) (SeqType BoxType)) (= (type t0@@7) TyType)) (= (type h@@8) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@19 (TSeq t0@@7) h@@8) (forall ((i@@1 Int) ) (!  (=> (and (<= 0 i@@1) (< i@@1 (|Seq#Length| v@@19))) ($IsAllocBox (|Seq#Index| v@@19 i@@1) t0@@7 h@@8))
 :qid |DafnyPre.235:11|
 :skolemid |379|
 :pattern ( (|Seq#Index| v@@19 i@@1))
))) (=> (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (|Seq#Length| v@@19))) ($IsAllocBox (|Seq#Index| v@@19 i@@2) t0@@7 h@@8))
 :qid |DafnyPre.235:11|
 :skolemid |379|
 :pattern ( (|Seq#Index| v@@19 i@@2))
)) ($IsAlloc v@@19 (TSeq t0@@7) h@@8))))
 :qid |DafnyPre.233:15|
 :skolemid |380|
 :pattern ( ($IsAlloc v@@19 (TSeq t0@@7) h@@8))
)))
(assert  (and (forall ((arg0@@51 T@U) ) (! (let ((V (MapTypeInv1 (type arg0@@51))))
(let ((U (MapTypeInv0 (type arg0@@51))))
(= (type (|Map#Elements| arg0@@51)) (MapType0Type U V))))
 :qid |funType:Map#Elements|
 :pattern ( (|Map#Elements| arg0@@51))
)) (forall ((arg0@@52 T@U) ) (! (let ((U@@0 (MapTypeInv0 (type arg0@@52))))
(= (type (|Map#Domain| arg0@@52)) (MapType0Type U@@0 boolType)))
 :qid |funType:Map#Domain|
 :pattern ( (|Map#Domain| arg0@@52))
))))
(assert (forall ((v@@20 T@U) (t0@@8 T@U) (t1 T@U) ) (!  (=> (and (and (= (type v@@20) (MapType BoxType BoxType)) (= (type t0@@8) TyType)) (= (type t1) TyType)) (and (=> ($Is v@@20 (TMap t0@@8 t1)) (forall ((bx@@21 T@U) ) (!  (=> (and (= (type bx@@21) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@20) bx@@21))) (and ($IsBox (MapType0Select (|Map#Elements| v@@20) bx@@21) t1) ($IsBox bx@@21 t0@@8)))
 :qid |DafnyPre.242:19|
 :skolemid |381|
 :pattern ( (MapType0Select (|Map#Elements| v@@20) bx@@21))
 :pattern ( (MapType0Select (|Map#Domain| v@@20) bx@@21))
))) (=> (forall ((bx@@22 T@U) ) (!  (=> (and (= (type bx@@22) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@20) bx@@22))) (and ($IsBox (MapType0Select (|Map#Elements| v@@20) bx@@22) t1) ($IsBox bx@@22 t0@@8)))
 :qid |DafnyPre.242:19|
 :skolemid |381|
 :pattern ( (MapType0Select (|Map#Elements| v@@20) bx@@22))
 :pattern ( (MapType0Select (|Map#Domain| v@@20) bx@@22))
)) ($Is v@@20 (TMap t0@@8 t1)))))
 :qid |DafnyPre.239:15|
 :skolemid |382|
 :pattern ( ($Is v@@20 (TMap t0@@8 t1)))
)))
(assert (forall ((v@@21 T@U) (t0@@9 T@U) (t1@@0 T@U) (h@@9 T@U) ) (!  (=> (and (and (and (= (type v@@21) (MapType BoxType BoxType)) (= (type t0@@9) TyType)) (= (type t1@@0) TyType)) (= (type h@@9) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9) (forall ((bx@@23 T@U) ) (!  (=> (and (= (type bx@@23) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@21) bx@@23))) (and ($IsAllocBox (MapType0Select (|Map#Elements| v@@21) bx@@23) t1@@0 h@@9) ($IsAllocBox bx@@23 t0@@9 h@@9)))
 :qid |DafnyPre.250:19|
 :skolemid |383|
 :pattern ( (MapType0Select (|Map#Elements| v@@21) bx@@23))
 :pattern ( (MapType0Select (|Map#Domain| v@@21) bx@@23))
))) (=> (forall ((bx@@24 T@U) ) (!  (=> (and (= (type bx@@24) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@21) bx@@24))) (and ($IsAllocBox (MapType0Select (|Map#Elements| v@@21) bx@@24) t1@@0 h@@9) ($IsAllocBox bx@@24 t0@@9 h@@9)))
 :qid |DafnyPre.250:19|
 :skolemid |383|
 :pattern ( (MapType0Select (|Map#Elements| v@@21) bx@@24))
 :pattern ( (MapType0Select (|Map#Domain| v@@21) bx@@24))
)) ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9))))
 :qid |DafnyPre.247:15|
 :skolemid |384|
 :pattern ( ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9))
)))
(assert  (and (forall ((arg0@@53 T@U) ) (! (let ((V@@0 (IMapTypeInv1 (type arg0@@53))))
(let ((U@@1 (IMapTypeInv0 (type arg0@@53))))
(= (type (|IMap#Elements| arg0@@53)) (MapType0Type U@@1 V@@0))))
 :qid |funType:IMap#Elements|
 :pattern ( (|IMap#Elements| arg0@@53))
)) (forall ((arg0@@54 T@U) ) (! (let ((U@@2 (IMapTypeInv0 (type arg0@@54))))
(= (type (|IMap#Domain| arg0@@54)) (MapType0Type U@@2 boolType)))
 :qid |funType:IMap#Domain|
 :pattern ( (|IMap#Domain| arg0@@54))
))))
(assert (forall ((v@@22 T@U) (t0@@10 T@U) (t1@@1 T@U) ) (!  (=> (and (and (= (type v@@22) (IMapType BoxType BoxType)) (= (type t0@@10) TyType)) (= (type t1@@1) TyType)) (and (=> ($Is v@@22 (TIMap t0@@10 t1@@1)) (forall ((bx@@25 T@U) ) (!  (=> (and (= (type bx@@25) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@22) bx@@25))) (and ($IsBox (MapType0Select (|IMap#Elements| v@@22) bx@@25) t1@@1) ($IsBox bx@@25 t0@@10)))
 :qid |DafnyPre.259:19|
 :skolemid |385|
 :pattern ( (MapType0Select (|IMap#Elements| v@@22) bx@@25))
 :pattern ( (MapType0Select (|IMap#Domain| v@@22) bx@@25))
))) (=> (forall ((bx@@26 T@U) ) (!  (=> (and (= (type bx@@26) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@22) bx@@26))) (and ($IsBox (MapType0Select (|IMap#Elements| v@@22) bx@@26) t1@@1) ($IsBox bx@@26 t0@@10)))
 :qid |DafnyPre.259:19|
 :skolemid |385|
 :pattern ( (MapType0Select (|IMap#Elements| v@@22) bx@@26))
 :pattern ( (MapType0Select (|IMap#Domain| v@@22) bx@@26))
)) ($Is v@@22 (TIMap t0@@10 t1@@1)))))
 :qid |DafnyPre.256:15|
 :skolemid |386|
 :pattern ( ($Is v@@22 (TIMap t0@@10 t1@@1)))
)))
(assert (forall ((v@@23 T@U) (t0@@11 T@U) (t1@@2 T@U) (h@@10 T@U) ) (!  (=> (and (and (and (= (type v@@23) (IMapType BoxType BoxType)) (= (type t0@@11) TyType)) (= (type t1@@2) TyType)) (= (type h@@10) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10) (forall ((bx@@27 T@U) ) (!  (=> (and (= (type bx@@27) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@23) bx@@27))) (and ($IsAllocBox (MapType0Select (|IMap#Elements| v@@23) bx@@27) t1@@2 h@@10) ($IsAllocBox bx@@27 t0@@11 h@@10)))
 :qid |DafnyPre.267:19|
 :skolemid |387|
 :pattern ( (MapType0Select (|IMap#Elements| v@@23) bx@@27))
 :pattern ( (MapType0Select (|IMap#Domain| v@@23) bx@@27))
))) (=> (forall ((bx@@28 T@U) ) (!  (=> (and (= (type bx@@28) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@23) bx@@28))) (and ($IsAllocBox (MapType0Select (|IMap#Elements| v@@23) bx@@28) t1@@2 h@@10) ($IsAllocBox bx@@28 t0@@11 h@@10)))
 :qid |DafnyPre.267:19|
 :skolemid |387|
 :pattern ( (MapType0Select (|IMap#Elements| v@@23) bx@@28))
 :pattern ( (MapType0Select (|IMap#Domain| v@@23) bx@@28))
)) ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10))))
 :qid |DafnyPre.264:15|
 :skolemid |388|
 :pattern ( ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10))
)))
(assert  (and (and (forall ((arg0@@55 T@U) (arg1@@17 T@U) ) (! (= (type (TypeTuple arg0@@55 arg1@@17)) ClassNameType)
 :qid |funType:TypeTuple|
 :pattern ( (TypeTuple arg0@@55 arg1@@17))
)) (forall ((arg0@@56 T@U) ) (! (= (type (TypeTupleCar arg0@@56)) ClassNameType)
 :qid |funType:TypeTupleCar|
 :pattern ( (TypeTupleCar arg0@@56))
))) (forall ((arg0@@57 T@U) ) (! (= (type (TypeTupleCdr arg0@@57)) ClassNameType)
 :qid |funType:TypeTupleCdr|
 :pattern ( (TypeTupleCdr arg0@@57))
))))
(assert (forall ((a@@1 T@U) (b@@1 T@U) ) (!  (=> (and (= (type a@@1) ClassNameType) (= (type b@@1) ClassNameType)) (and (= (TypeTupleCar (TypeTuple a@@1 b@@1)) a@@1) (= (TypeTupleCdr (TypeTuple a@@1 b@@1)) b@@1)))
 :qid |DafnyPre.292:15|
 :skolemid |389|
 :pattern ( (TypeTuple a@@1 b@@1))
)))
(assert (forall ((arg0@@58 T@U) ) (! (= (type (SetRef_to_SetBox arg0@@58)) (MapType0Type BoxType boolType))
 :qid |funType:SetRef_to_SetBox|
 :pattern ( (SetRef_to_SetBox arg0@@58))
)))
(assert (forall ((s@@1 T@U) (bx@@29 T@U) ) (!  (=> (and (= (type s@@1) (MapType0Type refType boolType)) (= (type bx@@29) BoxType)) (and (=> (U_2_bool (MapType0Select (SetRef_to_SetBox s@@1) bx@@29)) (U_2_bool (MapType0Select s@@1 ($Unbox refType bx@@29)))) (=> (U_2_bool (MapType0Select s@@1 ($Unbox refType bx@@29))) (U_2_bool (MapType0Select (SetRef_to_SetBox s@@1) bx@@29)))))
 :qid |DafnyPre.301:15|
 :skolemid |390|
 :pattern ( (MapType0Select (SetRef_to_SetBox s@@1) bx@@29))
)))
(assert (= (type Tclass._System.object?) TyType))
(assert (forall ((s@@2 T@U) ) (!  (=> (= (type s@@2) (MapType0Type refType boolType)) ($Is (SetRef_to_SetBox s@@2) (TSet Tclass._System.object?)))
 :qid |DafnyPre.303:15|
 :skolemid |391|
 :pattern ( (SetRef_to_SetBox s@@2))
)))
(assert (= (Ctor DatatypeTypeType) 20))
(assert (forall ((d T@U) ) (!  (=> (= (type d) DatatypeTypeType) (= (BoxRank ($Box d)) (DtRank d)))
 :qid |DafnyPre.322:15|
 :skolemid |392|
 :pattern ( (BoxRank ($Box d)))
)))
(assert (forall ((o T@U) ) (!  (=> (= (type o) BoxType) (<= 0 (|ORD#Offset| o)))
 :qid |DafnyPre.337:15|
 :skolemid |393|
 :pattern ( (|ORD#Offset| o))
)))
(assert (forall ((arg0@@59 Int) ) (! (= (type (|ORD#FromNat| arg0@@59)) BoxType)
 :qid |funType:ORD#FromNat|
 :pattern ( (|ORD#FromNat| arg0@@59))
)))
(assert (forall ((n@@0 Int) ) (!  (=> (<= 0 n@@0) (and (|ORD#IsNat| (|ORD#FromNat| n@@0)) (= (|ORD#Offset| (|ORD#FromNat| n@@0)) n@@0)))
 :qid |DafnyPre.343:15|
 :skolemid |394|
 :pattern ( (|ORD#FromNat| n@@0))
)))
(assert (forall ((o@@0 T@U) ) (!  (=> (and (= (type o@@0) BoxType) (|ORD#IsNat| o@@0)) (= o@@0 (|ORD#FromNat| (|ORD#Offset| o@@0))))
 :qid |DafnyPre.345:15|
 :skolemid |395|
 :pattern ( (|ORD#Offset| o@@0))
 :pattern ( (|ORD#IsNat| o@@0))
)))
(assert (forall ((o@@1 T@U) (p T@U) ) (!  (=> (and (= (type o@@1) BoxType) (= (type p) BoxType)) (and (and (and (=> (|ORD#Less| o@@1 p) (not (= o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (not (|ORD#IsNat| p))) (|ORD#Less| o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (|ORD#IsNat| p)) (and (=> (|ORD#Less| o@@1 p) (< (|ORD#Offset| o@@1) (|ORD#Offset| p))) (=> (< (|ORD#Offset| o@@1) (|ORD#Offset| p)) (|ORD#Less| o@@1 p))))) (=> (and (|ORD#Less| o@@1 p) (|ORD#IsNat| p)) (|ORD#IsNat| o@@1))))
 :qid |DafnyPre.349:15|
 :skolemid |396|
 :pattern ( (|ORD#Less| o@@1 p))
)))
(assert (forall ((o@@2 T@U) (p@@0 T@U) ) (!  (=> (and (= (type o@@2) BoxType) (= (type p@@0) BoxType)) (or (or (|ORD#Less| o@@2 p@@0) (= o@@2 p@@0)) (|ORD#Less| p@@0 o@@2)))
 :qid |DafnyPre.355:15|
 :skolemid |397|
 :pattern ( (|ORD#Less| o@@2 p@@0) (|ORD#Less| p@@0 o@@2))
)))
(assert (forall ((o@@3 T@U) (p@@1 T@U) (r T@U) ) (!  (=> (and (and (and (= (type o@@3) BoxType) (= (type p@@1) BoxType)) (= (type r) BoxType)) (and (|ORD#Less| o@@3 p@@1) (|ORD#Less| p@@1 r))) (|ORD#Less| o@@3 r))
 :qid |DafnyPre.358:15|
 :skolemid |398|
 :pattern ( (|ORD#Less| o@@3 p@@1) (|ORD#Less| p@@1 r))
 :pattern ( (|ORD#Less| o@@3 p@@1) (|ORD#Less| o@@3 r))
)))
(assert (forall ((o@@4 T@U) (p@@2 T@U) ) (!  (=> (and (= (type o@@4) BoxType) (= (type p@@2) BoxType)) (and (=> (|ORD#LessThanLimit| o@@4 p@@2) (|ORD#Less| o@@4 p@@2)) (=> (|ORD#Less| o@@4 p@@2) (|ORD#LessThanLimit| o@@4 p@@2))))
 :qid |DafnyPre.365:15|
 :skolemid |399|
 :pattern ( (|ORD#LessThanLimit| o@@4 p@@2))
)))
(assert (forall ((arg0@@60 T@U) (arg1@@18 T@U) ) (! (= (type (|ORD#Plus| arg0@@60 arg1@@18)) BoxType)
 :qid |funType:ORD#Plus|
 :pattern ( (|ORD#Plus| arg0@@60 arg1@@18))
)))
(assert (forall ((o@@5 T@U) (p@@3 T@U) ) (!  (=> (and (= (type o@@5) BoxType) (= (type p@@3) BoxType)) (and (=> (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)) (and (|ORD#IsNat| o@@5) (|ORD#IsNat| p@@3))) (=> (|ORD#IsNat| p@@3) (and (and (=> (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)) (|ORD#IsNat| o@@5)) (=> (|ORD#IsNat| o@@5) (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)))) (= (|ORD#Offset| (|ORD#Plus| o@@5 p@@3)) (+ (|ORD#Offset| o@@5) (|ORD#Offset| p@@3)))))))
 :qid |DafnyPre.369:15|
 :skolemid |400|
 :pattern ( (|ORD#Plus| o@@5 p@@3))
)))
(assert (forall ((o@@6 T@U) (p@@4 T@U) ) (!  (=> (and (= (type o@@6) BoxType) (= (type p@@4) BoxType)) (and (or (= o@@6 (|ORD#Plus| o@@6 p@@4)) (|ORD#Less| o@@6 (|ORD#Plus| o@@6 p@@4))) (or (= p@@4 (|ORD#Plus| o@@6 p@@4)) (|ORD#Less| p@@4 (|ORD#Plus| o@@6 p@@4)))))
 :qid |DafnyPre.374:15|
 :skolemid |401|
 :pattern ( (|ORD#Plus| o@@6 p@@4))
)))
(assert (forall ((o@@7 T@U) (p@@5 T@U) ) (!  (=> (and (= (type o@@7) BoxType) (= (type p@@5) BoxType)) (and (=> (= o@@7 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@7 p@@5) p@@5)) (=> (= p@@5 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@7 p@@5) o@@7))))
 :qid |DafnyPre.377:15|
 :skolemid |402|
 :pattern ( (|ORD#Plus| o@@7 p@@5))
)))
(assert (forall ((arg0@@61 T@U) (arg1@@19 T@U) ) (! (= (type (|ORD#Minus| arg0@@61 arg1@@19)) BoxType)
 :qid |funType:ORD#Minus|
 :pattern ( (|ORD#Minus| arg0@@61 arg1@@19))
)))
(assert (forall ((o@@8 T@U) (p@@6 T@U) ) (!  (=> (and (and (= (type o@@8) BoxType) (= (type p@@6) BoxType)) (and (|ORD#IsNat| p@@6) (<= (|ORD#Offset| p@@6) (|ORD#Offset| o@@8)))) (and (and (=> (|ORD#IsNat| (|ORD#Minus| o@@8 p@@6)) (|ORD#IsNat| o@@8)) (=> (|ORD#IsNat| o@@8) (|ORD#IsNat| (|ORD#Minus| o@@8 p@@6)))) (= (|ORD#Offset| (|ORD#Minus| o@@8 p@@6)) (- (|ORD#Offset| o@@8) (|ORD#Offset| p@@6)))))
 :qid |DafnyPre.382:15|
 :skolemid |403|
 :pattern ( (|ORD#Minus| o@@8 p@@6))
)))
(assert (forall ((o@@9 T@U) (p@@7 T@U) ) (!  (=> (and (and (= (type o@@9) BoxType) (= (type p@@7) BoxType)) (and (|ORD#IsNat| p@@7) (<= (|ORD#Offset| p@@7) (|ORD#Offset| o@@9)))) (or (and (= p@@7 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@9 p@@7) o@@9)) (and (not (= p@@7 (|ORD#FromNat| 0))) (|ORD#Less| (|ORD#Minus| o@@9 p@@7) o@@9))))
 :qid |DafnyPre.386:15|
 :skolemid |404|
 :pattern ( (|ORD#Minus| o@@9 p@@7))
)))
(assert (forall ((o@@10 T@U) (m@@5 Int) (n@@1 Int) ) (!  (=> (= (type o@@10) BoxType) (=> (and (<= 0 m@@5) (<= 0 n@@1)) (= (|ORD#Plus| (|ORD#Plus| o@@10 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n@@1)) (|ORD#Plus| o@@10 (|ORD#FromNat| (+ m@@5 n@@1))))))
 :qid |DafnyPre.392:15|
 :skolemid |405|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@10 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n@@1)))
)))
(assert (forall ((o@@11 T@U) (m@@6 Int) (n@@2 Int) ) (!  (=> (= (type o@@11) BoxType) (=> (and (and (<= 0 m@@6) (<= 0 n@@2)) (<= (+ m@@6 n@@2) (|ORD#Offset| o@@11))) (= (|ORD#Minus| (|ORD#Minus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@2)) (|ORD#Minus| o@@11 (|ORD#FromNat| (+ m@@6 n@@2))))))
 :qid |DafnyPre.397:15|
 :skolemid |406|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@2)))
)))
(assert (forall ((o@@12 T@U) (m@@7 Int) (n@@3 Int) ) (!  (=> (= (type o@@12) BoxType) (=> (and (and (<= 0 m@@7) (<= 0 n@@3)) (<= n@@3 (+ (|ORD#Offset| o@@12) m@@7))) (and (=> (<= 0 (- m@@7 n@@3)) (= (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)) (|ORD#Plus| o@@12 (|ORD#FromNat| (- m@@7 n@@3))))) (=> (<= (- m@@7 n@@3) 0) (= (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)) (|ORD#Minus| o@@12 (|ORD#FromNat| (- n@@3 m@@7))))))))
 :qid |DafnyPre.402:15|
 :skolemid |407|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)))
)))
(assert (forall ((o@@13 T@U) (m@@8 Int) (n@@4 Int) ) (!  (=> (= (type o@@13) BoxType) (=> (and (and (<= 0 m@@8) (<= 0 n@@4)) (<= n@@4 (+ (|ORD#Offset| o@@13) m@@8))) (and (=> (<= 0 (- m@@8 n@@4)) (= (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)) (|ORD#Minus| o@@13 (|ORD#FromNat| (- m@@8 n@@4))))) (=> (<= (- m@@8 n@@4) 0) (= (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)) (|ORD#Plus| o@@13 (|ORD#FromNat| (- n@@4 m@@8))))))))
 :qid |DafnyPre.408:15|
 :skolemid |408|
 :pattern ( (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)))
)))
(assert  (and (= (Ctor LayerTypeType) 21) (forall ((arg0@@62 T@U) (arg1@@20 T@U) ) (! (let ((A (MapType0TypeInv1 (type arg0@@62))))
(= (type (AtLayer arg0@@62 arg1@@20)) A))
 :qid |funType:AtLayer|
 :pattern ( (AtLayer arg0@@62 arg1@@20))
))))
(assert (forall ((f T@U) (ly T@U) ) (! (let ((A@@0 (MapType0TypeInv1 (type f))))
 (=> (and (= (type f) (MapType0Type LayerTypeType A@@0)) (= (type ly) LayerTypeType)) (= (AtLayer f ly) (MapType0Select f ly))))
 :qid |DafnyPre.432:18|
 :skolemid |409|
 :pattern ( (AtLayer f ly))
)))
(assert (forall ((arg0@@63 T@U) ) (! (= (type ($LS arg0@@63)) LayerTypeType)
 :qid |funType:$LS|
 :pattern ( ($LS arg0@@63))
)))
(assert (forall ((f@@0 T@U) (ly@@0 T@U) ) (! (let ((A@@1 (MapType0TypeInv1 (type f@@0))))
 (=> (and (= (type f@@0) (MapType0Type LayerTypeType A@@1)) (= (type ly@@0) LayerTypeType)) (= (AtLayer f@@0 ($LS ly@@0)) (AtLayer f@@0 ly@@0))))
 :qid |DafnyPre.433:18|
 :skolemid |410|
 :pattern ( (AtLayer f@@0 ($LS ly@@0)))
)))
(assert (forall ((arg0@@64 Int) ) (! (= (type (IndexField arg0@@64)) (FieldType BoxType))
 :qid |funType:IndexField|
 :pattern ( (IndexField arg0@@64))
)))
(assert (forall ((i@@3 Int) ) (! (= (FDim (IndexField i@@3)) 1)
 :qid |DafnyPre.444:15|
 :skolemid |411|
 :pattern ( (IndexField i@@3))
)))
(assert (forall ((i@@4 Int) ) (! (= (IndexField_Inverse (IndexField i@@4)) i@@4)
 :qid |DafnyPre.446:15|
 :skolemid |412|
 :pattern ( (IndexField i@@4))
)))
(assert (forall ((arg0@@65 T@U) (arg1@@21 Int) ) (! (= (type (MultiIndexField arg0@@65 arg1@@21)) (FieldType BoxType))
 :qid |funType:MultiIndexField|
 :pattern ( (MultiIndexField arg0@@65 arg1@@21))
)))
(assert (forall ((f@@1 T@U) (i@@5 Int) ) (!  (=> (= (type f@@1) (FieldType BoxType)) (= (FDim (MultiIndexField f@@1 i@@5)) (+ (FDim f@@1) 1)))
 :qid |DafnyPre.449:15|
 :skolemid |413|
 :pattern ( (MultiIndexField f@@1 i@@5))
)))
(assert (forall ((arg0@@66 T@U) ) (! (let ((T@@3 (FieldTypeInv0 (type arg0@@66))))
(= (type (MultiIndexField_Inverse0 arg0@@66)) (FieldType T@@3)))
 :qid |funType:MultiIndexField_Inverse0|
 :pattern ( (MultiIndexField_Inverse0 arg0@@66))
)))
(assert (forall ((f@@2 T@U) (i@@6 Int) ) (!  (=> (= (type f@@2) (FieldType BoxType)) (and (= (MultiIndexField_Inverse0 (MultiIndexField f@@2 i@@6)) f@@2) (= (MultiIndexField_Inverse1 (MultiIndexField f@@2 i@@6)) i@@6)))
 :qid |DafnyPre.452:15|
 :skolemid |414|
 :pattern ( (MultiIndexField f@@2 i@@6))
)))
(assert  (and (and (forall ((alpha@@3 T@T) (arg0@@67 T@U) (arg1@@22 T@U) ) (! (= (type (FieldOfDecl alpha@@3 arg0@@67 arg1@@22)) (FieldType alpha@@3))
 :qid |funType:FieldOfDecl|
 :pattern ( (FieldOfDecl alpha@@3 arg0@@67 arg1@@22))
)) (forall ((arg0@@68 T@U) ) (! (= (type (DeclType arg0@@68)) ClassNameType)
 :qid |funType:DeclType|
 :pattern ( (DeclType arg0@@68))
))) (forall ((arg0@@69 T@U) ) (! (= (type (DeclName arg0@@69)) NameFamilyType)
 :qid |funType:DeclName|
 :pattern ( (DeclName arg0@@69))
))))
(assert (forall ((cl T@U) (nm T@U) (T@@4 T@T) ) (!  (=> (and (= (type cl) ClassNameType) (= (type nm) NameFamilyType)) (and (= (DeclType (FieldOfDecl T@@4 cl nm)) cl) (= (DeclName (FieldOfDecl T@@4 cl nm)) nm)))
 :qid |DafnyPre.461:18|
 :skolemid |415|
 :pattern ( (FieldOfDecl T@@4 cl nm))
)))
(assert (forall ((h@@11 T@U) (k T@U) (v@@24 T@U) (t@@21 T@U) ) (!  (=> (and (and (and (and (= (type h@@11) (MapType0Type refType MapType1Type)) (= (type k) (MapType0Type refType MapType1Type))) (= (type t@@21) TyType)) ($HeapSucc h@@11 k)) ($IsAlloc v@@24 t@@21 h@@11)) ($IsAlloc v@@24 t@@21 k))
 :qid |DafnyPre.474:17|
 :skolemid |416|
 :pattern ( ($HeapSucc h@@11 k) ($IsAlloc v@@24 t@@21 h@@11))
)))
(assert (forall ((h@@12 T@U) (k@@0 T@U) (bx@@30 T@U) (t@@22 T@U) ) (!  (=> (and (and (and (and (and (= (type h@@12) (MapType0Type refType MapType1Type)) (= (type k@@0) (MapType0Type refType MapType1Type))) (= (type bx@@30) BoxType)) (= (type t@@22) TyType)) ($HeapSucc h@@12 k@@0)) ($IsAllocBox bx@@30 t@@22 h@@12)) ($IsAllocBox bx@@30 t@@22 k@@0))
 :qid |DafnyPre.477:14|
 :skolemid |417|
 :pattern ( ($HeapSucc h@@12 k@@0) ($IsAllocBox bx@@30 t@@22 h@@12))
)))
(assert (= (FDim alloc) 0))
(assert (= (DeclName alloc) allocName))
(assert  (not ($IsGhostField alloc)))
(assert (forall ((o@@14 T@U) ) (!  (=> (= (type o@@14) refType) (<= 0 (_System.array.Length o@@14)))
 :qid |DafnyPre.494:15|
 :skolemid |418|
 :no-pattern (type o@@14)
 :no-pattern (U_2_int o@@14)
 :no-pattern (U_2_bool o@@14)
)))
(assert (forall ((x@@15 Real) ) (! (= (q@Int x@@15) (to_int x@@15))
 :qid |DafnyPre.500:14|
 :skolemid |419|
 :pattern ( (q@Int x@@15))
)))
(assert (forall ((x@@16 Int) ) (! (= (q@Real x@@16) (to_real x@@16))
 :qid |DafnyPre.501:15|
 :skolemid |420|
 :pattern ( (q@Real x@@16))
)))
(assert (forall ((i@@7 Int) ) (! (= (q@Int (q@Real i@@7)) i@@7)
 :qid |DafnyPre.502:15|
 :skolemid |421|
 :pattern ( (q@Int (q@Real i@@7)))
)))
(assert (= (type $OneHeap) (MapType0Type refType MapType1Type)))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((h@@13 T@U) (r@@0 T@U) (f@@3 T@U) (x@@17 T@U) ) (! (let ((alpha@@4 (type x@@17)))
 (=> (and (and (and (= (type h@@13) (MapType0Type refType MapType1Type)) (= (type r@@0) refType)) (= (type f@@3) (FieldType alpha@@4))) ($IsGoodHeap (MapType0Store h@@13 r@@0 (MapType1Store (MapType0Select h@@13 r@@0) f@@3 x@@17)))) ($HeapSucc h@@13 (MapType0Store h@@13 r@@0 (MapType1Store (MapType0Select h@@13 r@@0) f@@3 x@@17)))))
 :qid |DafnyPre.524:22|
 :skolemid |422|
 :pattern ( (MapType0Store h@@13 r@@0 (MapType1Store (MapType0Select h@@13 r@@0) f@@3 x@@17)))
)))
(assert (forall ((a@@2 T@U) (b@@2 T@U) (c T@U) ) (!  (=> (and (and (and (and (= (type a@@2) (MapType0Type refType MapType1Type)) (= (type b@@2) (MapType0Type refType MapType1Type))) (= (type c) (MapType0Type refType MapType1Type))) (not (= a@@2 c))) (and ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))) ($HeapSucc a@@2 c))
 :qid |DafnyPre.527:15|
 :skolemid |423|
 :pattern ( ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))
)))
(assert (forall ((h@@14 T@U) (k@@1 T@U) ) (!  (=> (and (and (= (type h@@14) (MapType0Type refType MapType1Type)) (= (type k@@1) (MapType0Type refType MapType1Type))) ($HeapSucc h@@14 k@@1)) (forall ((o@@15 T@U) ) (!  (=> (and (= (type o@@15) refType) (U_2_bool (MapType1Select (MapType0Select h@@14 o@@15) alloc))) (U_2_bool (MapType1Select (MapType0Select k@@1 o@@15) alloc)))
 :qid |DafnyPre.530:30|
 :skolemid |424|
 :pattern ( (MapType1Select (MapType0Select k@@1 o@@15) alloc))
)))
 :qid |DafnyPre.529:15|
 :skolemid |425|
 :pattern ( ($HeapSucc h@@14 k@@1))
)))
(assert (forall ((h@@15 T@U) (k@@2 T@U) ) (!  (=> (and (and (= (type h@@15) (MapType0Type refType MapType1Type)) (= (type k@@2) (MapType0Type refType MapType1Type))) ($HeapSuccGhost h@@15 k@@2)) (and ($HeapSucc h@@15 k@@2) (forall ((o@@16 T@U) (f@@4 T@U) ) (! (let ((alpha@@5 (FieldTypeInv0 (type f@@4))))
 (=> (and (and (= (type o@@16) refType) (= (type f@@4) (FieldType alpha@@5))) (not ($IsGhostField f@@4))) (= (MapType1Select (MapType0Select h@@15 o@@16) f@@4) (MapType1Select (MapType0Select k@@2 o@@16) f@@4))))
 :qid |DafnyPre.536:20|
 :skolemid |426|
 :pattern ( (MapType1Select (MapType0Select k@@2 o@@16) f@@4))
))))
 :qid |DafnyPre.533:15|
 :skolemid |427|
 :pattern ( ($HeapSuccGhost h@@15 k@@2))
)))
(assert (forall ((s@@3 T@U) ) (! (let ((T@@5 (MapType0TypeInv0 (type s@@3))))
 (=> (= (type s@@3) (MapType0Type T@@5 boolType)) (<= 0 (|Set#Card| s@@3))))
 :qid |DafnyPre.594:18|
 :skolemid |432|
 :pattern ( (|Set#Card| s@@3))
)))
(assert (forall ((T@@6 T@T) ) (! (= (type (|Set#Empty| T@@6)) (MapType0Type T@@6 boolType))
 :qid |funType:Set#Empty|
 :pattern ( (|Set#Empty| T@@6))
)))
(assert (forall ((o@@17 T@U) ) (! (let ((T@@7 (type o@@17)))
 (not (U_2_bool (MapType0Select (|Set#Empty| T@@7) o@@17))))
 :qid |DafnyPre.597:18|
 :skolemid |433|
 :pattern ( (let ((T@@7 (type o@@17)))
(MapType0Select (|Set#Empty| T@@7) o@@17)))
)))
(assert (forall ((s@@4 T@U) ) (! (let ((T@@8 (MapType0TypeInv0 (type s@@4))))
 (=> (= (type s@@4) (MapType0Type T@@8 boolType)) (and (and (=> (= (|Set#Card| s@@4) 0) (= s@@4 (|Set#Empty| T@@8))) (=> (= s@@4 (|Set#Empty| T@@8)) (= (|Set#Card| s@@4) 0))) (=> (not (= (|Set#Card| s@@4) 0)) (exists ((x@@18 T@U) ) (!  (and (= (type x@@18) T@@8) (U_2_bool (MapType0Select s@@4 x@@18)))
 :qid |DafnyPre.600:33|
 :skolemid |434|
 :no-pattern (type x@@18)
 :no-pattern (U_2_int x@@18)
 :no-pattern (U_2_bool x@@18)
))))))
 :qid |DafnyPre.598:18|
 :skolemid |435|
 :pattern ( (|Set#Card| s@@4))
)))
(assert (forall ((arg0@@70 T@U) ) (! (let ((T@@9 (type arg0@@70)))
(= (type (|Set#Singleton| arg0@@70)) (MapType0Type T@@9 boolType)))
 :qid |funType:Set#Singleton|
 :pattern ( (|Set#Singleton| arg0@@70))
)))
(assert (forall ((r@@1 T@U) ) (! (U_2_bool (MapType0Select (|Set#Singleton| r@@1) r@@1))
 :qid |DafnyPre.606:18|
 :skolemid |436|
 :pattern ( (|Set#Singleton| r@@1))
)))
(assert (forall ((r@@2 T@U) (o@@18 T@U) ) (! (let ((T@@10 (type r@@2)))
 (=> (= (type o@@18) T@@10) (and (=> (U_2_bool (MapType0Select (|Set#Singleton| r@@2) o@@18)) (= r@@2 o@@18)) (=> (= r@@2 o@@18) (U_2_bool (MapType0Select (|Set#Singleton| r@@2) o@@18))))))
 :qid |DafnyPre.607:18|
 :skolemid |437|
 :pattern ( (MapType0Select (|Set#Singleton| r@@2) o@@18))
)))
(assert (forall ((r@@3 T@U) ) (! (= (|Set#Card| (|Set#Singleton| r@@3)) 1)
 :qid |DafnyPre.608:18|
 :skolemid |438|
 :pattern ( (|Set#Card| (|Set#Singleton| r@@3)))
)))
(assert (forall ((arg0@@71 T@U) (arg1@@23 T@U) ) (! (let ((T@@11 (type arg1@@23)))
(= (type (|Set#UnionOne| arg0@@71 arg1@@23)) (MapType0Type T@@11 boolType)))
 :qid |funType:Set#UnionOne|
 :pattern ( (|Set#UnionOne| arg0@@71 arg1@@23))
)))
(assert (forall ((a@@3 T@U) (x@@19 T@U) (o@@19 T@U) ) (! (let ((T@@12 (type x@@19)))
 (=> (and (= (type a@@3) (MapType0Type T@@12 boolType)) (= (type o@@19) T@@12)) (and (=> (U_2_bool (MapType0Select (|Set#UnionOne| a@@3 x@@19) o@@19)) (or (= o@@19 x@@19) (U_2_bool (MapType0Select a@@3 o@@19)))) (=> (or (= o@@19 x@@19) (U_2_bool (MapType0Select a@@3 o@@19))) (U_2_bool (MapType0Select (|Set#UnionOne| a@@3 x@@19) o@@19))))))
 :qid |DafnyPre.611:18|
 :skolemid |439|
 :pattern ( (MapType0Select (|Set#UnionOne| a@@3 x@@19) o@@19))
)))
(assert (forall ((a@@4 T@U) (x@@20 T@U) ) (! (let ((T@@13 (type x@@20)))
 (=> (= (type a@@4) (MapType0Type T@@13 boolType)) (U_2_bool (MapType0Select (|Set#UnionOne| a@@4 x@@20) x@@20))))
 :qid |DafnyPre.613:18|
 :skolemid |440|
 :pattern ( (|Set#UnionOne| a@@4 x@@20))
)))
(assert (forall ((a@@5 T@U) (x@@21 T@U) (y@@1 T@U) ) (! (let ((T@@14 (type x@@21)))
 (=> (and (and (= (type a@@5) (MapType0Type T@@14 boolType)) (= (type y@@1) T@@14)) (U_2_bool (MapType0Select a@@5 y@@1))) (U_2_bool (MapType0Select (|Set#UnionOne| a@@5 x@@21) y@@1))))
 :qid |DafnyPre.615:18|
 :skolemid |441|
 :pattern ( (|Set#UnionOne| a@@5 x@@21) (MapType0Select a@@5 y@@1))
)))
(assert (forall ((a@@6 T@U) (x@@22 T@U) ) (! (let ((T@@15 (type x@@22)))
 (=> (and (= (type a@@6) (MapType0Type T@@15 boolType)) (U_2_bool (MapType0Select a@@6 x@@22))) (= (|Set#Card| (|Set#UnionOne| a@@6 x@@22)) (|Set#Card| a@@6))))
 :qid |DafnyPre.617:18|
 :skolemid |442|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@6 x@@22)))
)))
(assert (forall ((a@@7 T@U) (x@@23 T@U) ) (! (let ((T@@16 (type x@@23)))
 (=> (and (= (type a@@7) (MapType0Type T@@16 boolType)) (not (U_2_bool (MapType0Select a@@7 x@@23)))) (= (|Set#Card| (|Set#UnionOne| a@@7 x@@23)) (+ (|Set#Card| a@@7) 1))))
 :qid |DafnyPre.619:18|
 :skolemid |443|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@7 x@@23)))
)))
(assert (forall ((arg0@@72 T@U) (arg1@@24 T@U) ) (! (let ((T@@17 (MapType0TypeInv0 (type arg0@@72))))
(= (type (|Set#Union| arg0@@72 arg1@@24)) (MapType0Type T@@17 boolType)))
 :qid |funType:Set#Union|
 :pattern ( (|Set#Union| arg0@@72 arg1@@24))
)))
(assert (forall ((a@@8 T@U) (b@@3 T@U) (o@@20 T@U) ) (! (let ((T@@18 (type o@@20)))
 (=> (and (= (type a@@8) (MapType0Type T@@18 boolType)) (= (type b@@3) (MapType0Type T@@18 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Union| a@@8 b@@3) o@@20)) (or (U_2_bool (MapType0Select a@@8 o@@20)) (U_2_bool (MapType0Select b@@3 o@@20)))) (=> (or (U_2_bool (MapType0Select a@@8 o@@20)) (U_2_bool (MapType0Select b@@3 o@@20))) (U_2_bool (MapType0Select (|Set#Union| a@@8 b@@3) o@@20))))))
 :qid |DafnyPre.623:18|
 :skolemid |444|
 :pattern ( (MapType0Select (|Set#Union| a@@8 b@@3) o@@20))
)))
(assert (forall ((a@@9 T@U) (b@@4 T@U) (y@@2 T@U) ) (! (let ((T@@19 (type y@@2)))
 (=> (and (and (= (type a@@9) (MapType0Type T@@19 boolType)) (= (type b@@4) (MapType0Type T@@19 boolType))) (U_2_bool (MapType0Select a@@9 y@@2))) (U_2_bool (MapType0Select (|Set#Union| a@@9 b@@4) y@@2))))
 :qid |DafnyPre.625:18|
 :skolemid |445|
 :pattern ( (|Set#Union| a@@9 b@@4) (MapType0Select a@@9 y@@2))
)))
(assert (forall ((a@@10 T@U) (b@@5 T@U) (y@@3 T@U) ) (! (let ((T@@20 (type y@@3)))
 (=> (and (and (= (type a@@10) (MapType0Type T@@20 boolType)) (= (type b@@5) (MapType0Type T@@20 boolType))) (U_2_bool (MapType0Select b@@5 y@@3))) (U_2_bool (MapType0Select (|Set#Union| a@@10 b@@5) y@@3))))
 :qid |DafnyPre.627:18|
 :skolemid |446|
 :pattern ( (|Set#Union| a@@10 b@@5) (MapType0Select b@@5 y@@3))
)))
(assert (forall ((arg0@@73 T@U) (arg1@@25 T@U) ) (! (let ((T@@21 (MapType0TypeInv0 (type arg0@@73))))
(= (type (|Set#Difference| arg0@@73 arg1@@25)) (MapType0Type T@@21 boolType)))
 :qid |funType:Set#Difference|
 :pattern ( (|Set#Difference| arg0@@73 arg1@@25))
)))
(assert (forall ((a@@11 T@U) (b@@6 T@U) ) (! (let ((T@@22 (MapType0TypeInv0 (type a@@11))))
 (=> (and (and (= (type a@@11) (MapType0Type T@@22 boolType)) (= (type b@@6) (MapType0Type T@@22 boolType))) (|Set#Disjoint| a@@11 b@@6)) (and (= (|Set#Difference| (|Set#Union| a@@11 b@@6) a@@11) b@@6) (= (|Set#Difference| (|Set#Union| a@@11 b@@6) b@@6) a@@11))))
 :qid |DafnyPre.629:18|
 :skolemid |447|
 :pattern ( (|Set#Union| a@@11 b@@6))
)))
(assert (forall ((arg0@@74 T@U) (arg1@@26 T@U) ) (! (let ((T@@23 (MapType0TypeInv0 (type arg0@@74))))
(= (type (|Set#Intersection| arg0@@74 arg1@@26)) (MapType0Type T@@23 boolType)))
 :qid |funType:Set#Intersection|
 :pattern ( (|Set#Intersection| arg0@@74 arg1@@26))
)))
(assert (forall ((a@@12 T@U) (b@@7 T@U) (o@@21 T@U) ) (! (let ((T@@24 (type o@@21)))
 (=> (and (= (type a@@12) (MapType0Type T@@24 boolType)) (= (type b@@7) (MapType0Type T@@24 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@21)) (and (U_2_bool (MapType0Select a@@12 o@@21)) (U_2_bool (MapType0Select b@@7 o@@21)))) (=> (and (U_2_bool (MapType0Select a@@12 o@@21)) (U_2_bool (MapType0Select b@@7 o@@21))) (U_2_bool (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@21))))))
 :qid |DafnyPre.639:18|
 :skolemid |448|
 :pattern ( (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@21))
)))
(assert (forall ((a@@13 T@U) (b@@8 T@U) ) (! (let ((T@@25 (MapType0TypeInv0 (type a@@13))))
 (=> (and (= (type a@@13) (MapType0Type T@@25 boolType)) (= (type b@@8) (MapType0Type T@@25 boolType))) (= (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8) (|Set#Union| a@@13 b@@8))))
 :qid |DafnyPre.642:18|
 :skolemid |449|
 :pattern ( (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8))
)))
(assert (forall ((a@@14 T@U) (b@@9 T@U) ) (! (let ((T@@26 (MapType0TypeInv0 (type a@@14))))
 (=> (and (= (type a@@14) (MapType0Type T@@26 boolType)) (= (type b@@9) (MapType0Type T@@26 boolType))) (= (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)) (|Set#Union| a@@14 b@@9))))
 :qid |DafnyPre.644:18|
 :skolemid |450|
 :pattern ( (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)))
)))
(assert (forall ((a@@15 T@U) (b@@10 T@U) ) (! (let ((T@@27 (MapType0TypeInv0 (type a@@15))))
 (=> (and (= (type a@@15) (MapType0Type T@@27 boolType)) (= (type b@@10) (MapType0Type T@@27 boolType))) (= (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10) (|Set#Intersection| a@@15 b@@10))))
 :qid |DafnyPre.646:18|
 :skolemid |451|
 :pattern ( (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10))
)))
(assert (forall ((a@@16 T@U) (b@@11 T@U) ) (! (let ((T@@28 (MapType0TypeInv0 (type a@@16))))
 (=> (and (= (type a@@16) (MapType0Type T@@28 boolType)) (= (type b@@11) (MapType0Type T@@28 boolType))) (= (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)) (|Set#Intersection| a@@16 b@@11))))
 :qid |DafnyPre.648:18|
 :skolemid |452|
 :pattern ( (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)))
)))
(assert (forall ((a@@17 T@U) (b@@12 T@U) ) (! (let ((T@@29 (MapType0TypeInv0 (type a@@17))))
 (=> (and (= (type a@@17) (MapType0Type T@@29 boolType)) (= (type b@@12) (MapType0Type T@@29 boolType))) (= (+ (|Set#Card| (|Set#Union| a@@17 b@@12)) (|Set#Card| (|Set#Intersection| a@@17 b@@12))) (+ (|Set#Card| a@@17) (|Set#Card| b@@12)))))
 :qid |DafnyPre.650:18|
 :skolemid |453|
 :pattern ( (|Set#Card| (|Set#Union| a@@17 b@@12)))
 :pattern ( (|Set#Card| (|Set#Intersection| a@@17 b@@12)))
)))
(assert (forall ((a@@18 T@U) (b@@13 T@U) (o@@22 T@U) ) (! (let ((T@@30 (type o@@22)))
 (=> (and (= (type a@@18) (MapType0Type T@@30 boolType)) (= (type b@@13) (MapType0Type T@@30 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22)) (and (U_2_bool (MapType0Select a@@18 o@@22)) (not (U_2_bool (MapType0Select b@@13 o@@22))))) (=> (and (U_2_bool (MapType0Select a@@18 o@@22)) (not (U_2_bool (MapType0Select b@@13 o@@22)))) (U_2_bool (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22))))))
 :qid |DafnyPre.654:18|
 :skolemid |454|
 :pattern ( (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22))
)))
(assert (forall ((a@@19 T@U) (b@@14 T@U) (y@@4 T@U) ) (! (let ((T@@31 (type y@@4)))
 (=> (and (and (= (type a@@19) (MapType0Type T@@31 boolType)) (= (type b@@14) (MapType0Type T@@31 boolType))) (U_2_bool (MapType0Select b@@14 y@@4))) (not (U_2_bool (MapType0Select (|Set#Difference| a@@19 b@@14) y@@4)))))
 :qid |DafnyPre.656:18|
 :skolemid |455|
 :pattern ( (|Set#Difference| a@@19 b@@14) (MapType0Select b@@14 y@@4))
)))
(assert (forall ((a@@20 T@U) (b@@15 T@U) ) (! (let ((T@@32 (MapType0TypeInv0 (type a@@20))))
 (=> (and (= (type a@@20) (MapType0Type T@@32 boolType)) (= (type b@@15) (MapType0Type T@@32 boolType))) (and (= (+ (+ (|Set#Card| (|Set#Difference| a@@20 b@@15)) (|Set#Card| (|Set#Difference| b@@15 a@@20))) (|Set#Card| (|Set#Intersection| a@@20 b@@15))) (|Set#Card| (|Set#Union| a@@20 b@@15))) (= (|Set#Card| (|Set#Difference| a@@20 b@@15)) (- (|Set#Card| a@@20) (|Set#Card| (|Set#Intersection| a@@20 b@@15)))))))
 :qid |DafnyPre.658:18|
 :skolemid |456|
 :pattern ( (|Set#Card| (|Set#Difference| a@@20 b@@15)))
)))
(assert (forall ((a@@21 T@U) (b@@16 T@U) ) (! (let ((T@@33 (MapType0TypeInv0 (type a@@21))))
 (=> (and (= (type a@@21) (MapType0Type T@@33 boolType)) (= (type b@@16) (MapType0Type T@@33 boolType))) (and (=> (|Set#Subset| a@@21 b@@16) (forall ((o@@23 T@U) ) (!  (=> (and (= (type o@@23) T@@33) (U_2_bool (MapType0Select a@@21 o@@23))) (U_2_bool (MapType0Select b@@16 o@@23)))
 :qid |DafnyPre.667:32|
 :skolemid |457|
 :pattern ( (MapType0Select a@@21 o@@23))
 :pattern ( (MapType0Select b@@16 o@@23))
))) (=> (forall ((o@@24 T@U) ) (!  (=> (and (= (type o@@24) T@@33) (U_2_bool (MapType0Select a@@21 o@@24))) (U_2_bool (MapType0Select b@@16 o@@24)))
 :qid |DafnyPre.667:32|
 :skolemid |457|
 :pattern ( (MapType0Select a@@21 o@@24))
 :pattern ( (MapType0Select b@@16 o@@24))
)) (|Set#Subset| a@@21 b@@16)))))
 :qid |DafnyPre.666:17|
 :skolemid |458|
 :pattern ( (|Set#Subset| a@@21 b@@16))
)))
(assert (forall ((a@@22 T@U) (b@@17 T@U) ) (! (let ((T@@34 (MapType0TypeInv0 (type a@@22))))
 (=> (and (= (type a@@22) (MapType0Type T@@34 boolType)) (= (type b@@17) (MapType0Type T@@34 boolType))) (and (=> (|Set#Equal| a@@22 b@@17) (forall ((o@@25 T@U) ) (!  (=> (= (type o@@25) T@@34) (and (=> (U_2_bool (MapType0Select a@@22 o@@25)) (U_2_bool (MapType0Select b@@17 o@@25))) (=> (U_2_bool (MapType0Select b@@17 o@@25)) (U_2_bool (MapType0Select a@@22 o@@25)))))
 :qid |DafnyPre.675:31|
 :skolemid |459|
 :pattern ( (MapType0Select a@@22 o@@25))
 :pattern ( (MapType0Select b@@17 o@@25))
))) (=> (forall ((o@@26 T@U) ) (!  (=> (= (type o@@26) T@@34) (and (=> (U_2_bool (MapType0Select a@@22 o@@26)) (U_2_bool (MapType0Select b@@17 o@@26))) (=> (U_2_bool (MapType0Select b@@17 o@@26)) (U_2_bool (MapType0Select a@@22 o@@26)))))
 :qid |DafnyPre.675:31|
 :skolemid |459|
 :pattern ( (MapType0Select a@@22 o@@26))
 :pattern ( (MapType0Select b@@17 o@@26))
)) (|Set#Equal| a@@22 b@@17)))))
 :qid |DafnyPre.674:17|
 :skolemid |460|
 :pattern ( (|Set#Equal| a@@22 b@@17))
)))
(assert (forall ((a@@23 T@U) (b@@18 T@U) ) (! (let ((T@@35 (MapType0TypeInv0 (type a@@23))))
 (=> (and (and (= (type a@@23) (MapType0Type T@@35 boolType)) (= (type b@@18) (MapType0Type T@@35 boolType))) (|Set#Equal| a@@23 b@@18)) (= a@@23 b@@18)))
 :qid |DafnyPre.676:17|
 :skolemid |461|
 :pattern ( (|Set#Equal| a@@23 b@@18))
)))
(assert (forall ((a@@24 T@U) (b@@19 T@U) ) (! (let ((T@@36 (MapType0TypeInv0 (type a@@24))))
 (=> (and (= (type a@@24) (MapType0Type T@@36 boolType)) (= (type b@@19) (MapType0Type T@@36 boolType))) (and (=> (|Set#Disjoint| a@@24 b@@19) (forall ((o@@27 T@U) ) (!  (=> (= (type o@@27) T@@36) (or (not (U_2_bool (MapType0Select a@@24 o@@27))) (not (U_2_bool (MapType0Select b@@19 o@@27)))))
 :qid |DafnyPre.681:34|
 :skolemid |462|
 :pattern ( (MapType0Select a@@24 o@@27))
 :pattern ( (MapType0Select b@@19 o@@27))
))) (=> (forall ((o@@28 T@U) ) (!  (=> (= (type o@@28) T@@36) (or (not (U_2_bool (MapType0Select a@@24 o@@28))) (not (U_2_bool (MapType0Select b@@19 o@@28)))))
 :qid |DafnyPre.681:34|
 :skolemid |462|
 :pattern ( (MapType0Select a@@24 o@@28))
 :pattern ( (MapType0Select b@@19 o@@28))
)) (|Set#Disjoint| a@@24 b@@19)))))
 :qid |DafnyPre.680:18|
 :skolemid |463|
 :pattern ( (|Set#Disjoint| a@@24 b@@19))
)))
(assert (forall ((T@@37 T@T) ) (! (= (type (|ISet#Empty| T@@37)) (MapType0Type T@@37 boolType))
 :qid |funType:ISet#Empty|
 :pattern ( (|ISet#Empty| T@@37))
)))
(assert (forall ((o@@29 T@U) ) (! (let ((T@@38 (type o@@29)))
 (not (U_2_bool (MapType0Select (|ISet#Empty| T@@38) o@@29))))
 :qid |DafnyPre.690:18|
 :skolemid |464|
 :pattern ( (let ((T@@38 (type o@@29)))
(MapType0Select (|ISet#Empty| T@@38) o@@29)))
)))
(assert (forall ((arg0@@75 T@U) (arg1@@27 T@U) ) (! (let ((T@@39 (type arg1@@27)))
(= (type (|ISet#UnionOne| arg0@@75 arg1@@27)) (MapType0Type T@@39 boolType)))
 :qid |funType:ISet#UnionOne|
 :pattern ( (|ISet#UnionOne| arg0@@75 arg1@@27))
)))
(assert (forall ((a@@25 T@U) (x@@24 T@U) (o@@30 T@U) ) (! (let ((T@@40 (type x@@24)))
 (=> (and (= (type a@@25) (MapType0Type T@@40 boolType)) (= (type o@@30) T@@40)) (and (=> (U_2_bool (MapType0Select (|ISet#UnionOne| a@@25 x@@24) o@@30)) (or (= o@@30 x@@24) (U_2_bool (MapType0Select a@@25 o@@30)))) (=> (or (= o@@30 x@@24) (U_2_bool (MapType0Select a@@25 o@@30))) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@25 x@@24) o@@30))))))
 :qid |DafnyPre.697:18|
 :skolemid |465|
 :pattern ( (MapType0Select (|ISet#UnionOne| a@@25 x@@24) o@@30))
)))
(assert (forall ((a@@26 T@U) (x@@25 T@U) ) (! (let ((T@@41 (type x@@25)))
 (=> (= (type a@@26) (MapType0Type T@@41 boolType)) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@26 x@@25) x@@25))))
 :qid |DafnyPre.699:18|
 :skolemid |466|
 :pattern ( (|ISet#UnionOne| a@@26 x@@25))
)))
(assert (forall ((a@@27 T@U) (x@@26 T@U) (y@@5 T@U) ) (! (let ((T@@42 (type x@@26)))
 (=> (and (and (= (type a@@27) (MapType0Type T@@42 boolType)) (= (type y@@5) T@@42)) (U_2_bool (MapType0Select a@@27 y@@5))) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@27 x@@26) y@@5))))
 :qid |DafnyPre.701:18|
 :skolemid |467|
 :pattern ( (|ISet#UnionOne| a@@27 x@@26) (MapType0Select a@@27 y@@5))
)))
(assert (forall ((arg0@@76 T@U) (arg1@@28 T@U) ) (! (let ((T@@43 (MapType0TypeInv0 (type arg0@@76))))
(= (type (|ISet#Union| arg0@@76 arg1@@28)) (MapType0Type T@@43 boolType)))
 :qid |funType:ISet#Union|
 :pattern ( (|ISet#Union| arg0@@76 arg1@@28))
)))
(assert (forall ((a@@28 T@U) (b@@20 T@U) (o@@31 T@U) ) (! (let ((T@@44 (type o@@31)))
 (=> (and (= (type a@@28) (MapType0Type T@@44 boolType)) (= (type b@@20) (MapType0Type T@@44 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Union| a@@28 b@@20) o@@31)) (or (U_2_bool (MapType0Select a@@28 o@@31)) (U_2_bool (MapType0Select b@@20 o@@31)))) (=> (or (U_2_bool (MapType0Select a@@28 o@@31)) (U_2_bool (MapType0Select b@@20 o@@31))) (U_2_bool (MapType0Select (|ISet#Union| a@@28 b@@20) o@@31))))))
 :qid |DafnyPre.705:18|
 :skolemid |468|
 :pattern ( (MapType0Select (|ISet#Union| a@@28 b@@20) o@@31))
)))
(assert (forall ((a@@29 T@U) (b@@21 T@U) (y@@6 T@U) ) (! (let ((T@@45 (type y@@6)))
 (=> (and (and (= (type a@@29) (MapType0Type T@@45 boolType)) (= (type b@@21) (MapType0Type T@@45 boolType))) (U_2_bool (MapType0Select a@@29 y@@6))) (U_2_bool (MapType0Select (|ISet#Union| a@@29 b@@21) y@@6))))
 :qid |DafnyPre.707:18|
 :skolemid |469|
 :pattern ( (|ISet#Union| a@@29 b@@21) (MapType0Select a@@29 y@@6))
)))
(assert (forall ((a@@30 T@U) (b@@22 T@U) (y@@7 T@U) ) (! (let ((T@@46 (type y@@7)))
 (=> (and (and (= (type a@@30) (MapType0Type T@@46 boolType)) (= (type b@@22) (MapType0Type T@@46 boolType))) (U_2_bool (MapType0Select b@@22 y@@7))) (U_2_bool (MapType0Select (|ISet#Union| a@@30 b@@22) y@@7))))
 :qid |DafnyPre.709:18|
 :skolemid |470|
 :pattern ( (|ISet#Union| a@@30 b@@22) (MapType0Select b@@22 y@@7))
)))
(assert (forall ((arg0@@77 T@U) (arg1@@29 T@U) ) (! (let ((T@@47 (MapType0TypeInv0 (type arg0@@77))))
(= (type (|ISet#Difference| arg0@@77 arg1@@29)) (MapType0Type T@@47 boolType)))
 :qid |funType:ISet#Difference|
 :pattern ( (|ISet#Difference| arg0@@77 arg1@@29))
)))
(assert (forall ((a@@31 T@U) (b@@23 T@U) ) (! (let ((T@@48 (MapType0TypeInv0 (type a@@31))))
 (=> (and (and (= (type a@@31) (MapType0Type T@@48 boolType)) (= (type b@@23) (MapType0Type T@@48 boolType))) (|ISet#Disjoint| a@@31 b@@23)) (and (= (|ISet#Difference| (|ISet#Union| a@@31 b@@23) a@@31) b@@23) (= (|ISet#Difference| (|ISet#Union| a@@31 b@@23) b@@23) a@@31))))
 :qid |DafnyPre.711:18|
 :skolemid |471|
 :pattern ( (|ISet#Union| a@@31 b@@23))
)))
(assert (forall ((arg0@@78 T@U) (arg1@@30 T@U) ) (! (let ((T@@49 (MapType0TypeInv0 (type arg0@@78))))
(= (type (|ISet#Intersection| arg0@@78 arg1@@30)) (MapType0Type T@@49 boolType)))
 :qid |funType:ISet#Intersection|
 :pattern ( (|ISet#Intersection| arg0@@78 arg1@@30))
)))
(assert (forall ((a@@32 T@U) (b@@24 T@U) (o@@32 T@U) ) (! (let ((T@@50 (type o@@32)))
 (=> (and (= (type a@@32) (MapType0Type T@@50 boolType)) (= (type b@@24) (MapType0Type T@@50 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@32)) (and (U_2_bool (MapType0Select a@@32 o@@32)) (U_2_bool (MapType0Select b@@24 o@@32)))) (=> (and (U_2_bool (MapType0Select a@@32 o@@32)) (U_2_bool (MapType0Select b@@24 o@@32))) (U_2_bool (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@32))))))
 :qid |DafnyPre.721:18|
 :skolemid |472|
 :pattern ( (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@32))
)))
(assert (forall ((a@@33 T@U) (b@@25 T@U) ) (! (let ((T@@51 (MapType0TypeInv0 (type a@@33))))
 (=> (and (= (type a@@33) (MapType0Type T@@51 boolType)) (= (type b@@25) (MapType0Type T@@51 boolType))) (= (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25) (|ISet#Union| a@@33 b@@25))))
 :qid |DafnyPre.724:18|
 :skolemid |473|
 :pattern ( (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25))
)))
(assert (forall ((a@@34 T@U) (b@@26 T@U) ) (! (let ((T@@52 (MapType0TypeInv0 (type a@@34))))
 (=> (and (= (type a@@34) (MapType0Type T@@52 boolType)) (= (type b@@26) (MapType0Type T@@52 boolType))) (= (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)) (|ISet#Union| a@@34 b@@26))))
 :qid |DafnyPre.726:18|
 :skolemid |474|
 :pattern ( (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)))
)))
(assert (forall ((a@@35 T@U) (b@@27 T@U) ) (! (let ((T@@53 (MapType0TypeInv0 (type a@@35))))
 (=> (and (= (type a@@35) (MapType0Type T@@53 boolType)) (= (type b@@27) (MapType0Type T@@53 boolType))) (= (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27) (|ISet#Intersection| a@@35 b@@27))))
 :qid |DafnyPre.728:18|
 :skolemid |475|
 :pattern ( (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27))
)))
(assert (forall ((a@@36 T@U) (b@@28 T@U) ) (! (let ((T@@54 (MapType0TypeInv0 (type a@@36))))
 (=> (and (= (type a@@36) (MapType0Type T@@54 boolType)) (= (type b@@28) (MapType0Type T@@54 boolType))) (= (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)) (|ISet#Intersection| a@@36 b@@28))))
 :qid |DafnyPre.730:18|
 :skolemid |476|
 :pattern ( (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)))
)))
(assert (forall ((a@@37 T@U) (b@@29 T@U) (o@@33 T@U) ) (! (let ((T@@55 (type o@@33)))
 (=> (and (= (type a@@37) (MapType0Type T@@55 boolType)) (= (type b@@29) (MapType0Type T@@55 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@33)) (and (U_2_bool (MapType0Select a@@37 o@@33)) (not (U_2_bool (MapType0Select b@@29 o@@33))))) (=> (and (U_2_bool (MapType0Select a@@37 o@@33)) (not (U_2_bool (MapType0Select b@@29 o@@33)))) (U_2_bool (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@33))))))
 :qid |DafnyPre.735:18|
 :skolemid |477|
 :pattern ( (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@33))
)))
(assert (forall ((a@@38 T@U) (b@@30 T@U) (y@@8 T@U) ) (! (let ((T@@56 (type y@@8)))
 (=> (and (and (= (type a@@38) (MapType0Type T@@56 boolType)) (= (type b@@30) (MapType0Type T@@56 boolType))) (U_2_bool (MapType0Select b@@30 y@@8))) (not (U_2_bool (MapType0Select (|ISet#Difference| a@@38 b@@30) y@@8)))))
 :qid |DafnyPre.737:18|
 :skolemid |478|
 :pattern ( (|ISet#Difference| a@@38 b@@30) (MapType0Select b@@30 y@@8))
)))
(assert (forall ((a@@39 T@U) (b@@31 T@U) ) (! (let ((T@@57 (MapType0TypeInv0 (type a@@39))))
 (=> (and (= (type a@@39) (MapType0Type T@@57 boolType)) (= (type b@@31) (MapType0Type T@@57 boolType))) (and (=> (|ISet#Subset| a@@39 b@@31) (forall ((o@@34 T@U) ) (!  (=> (and (= (type o@@34) T@@57) (U_2_bool (MapType0Select a@@39 o@@34))) (U_2_bool (MapType0Select b@@31 o@@34)))
 :qid |DafnyPre.742:33|
 :skolemid |479|
 :pattern ( (MapType0Select a@@39 o@@34))
 :pattern ( (MapType0Select b@@31 o@@34))
))) (=> (forall ((o@@35 T@U) ) (!  (=> (and (= (type o@@35) T@@57) (U_2_bool (MapType0Select a@@39 o@@35))) (U_2_bool (MapType0Select b@@31 o@@35)))
 :qid |DafnyPre.742:33|
 :skolemid |479|
 :pattern ( (MapType0Select a@@39 o@@35))
 :pattern ( (MapType0Select b@@31 o@@35))
)) (|ISet#Subset| a@@39 b@@31)))))
 :qid |DafnyPre.741:17|
 :skolemid |480|
 :pattern ( (|ISet#Subset| a@@39 b@@31))
)))
(assert (forall ((a@@40 T@U) (b@@32 T@U) ) (! (let ((T@@58 (MapType0TypeInv0 (type a@@40))))
 (=> (and (= (type a@@40) (MapType0Type T@@58 boolType)) (= (type b@@32) (MapType0Type T@@58 boolType))) (and (=> (|ISet#Equal| a@@40 b@@32) (forall ((o@@36 T@U) ) (!  (=> (= (type o@@36) T@@58) (and (=> (U_2_bool (MapType0Select a@@40 o@@36)) (U_2_bool (MapType0Select b@@32 o@@36))) (=> (U_2_bool (MapType0Select b@@32 o@@36)) (U_2_bool (MapType0Select a@@40 o@@36)))))
 :qid |DafnyPre.750:32|
 :skolemid |481|
 :pattern ( (MapType0Select a@@40 o@@36))
 :pattern ( (MapType0Select b@@32 o@@36))
))) (=> (forall ((o@@37 T@U) ) (!  (=> (= (type o@@37) T@@58) (and (=> (U_2_bool (MapType0Select a@@40 o@@37)) (U_2_bool (MapType0Select b@@32 o@@37))) (=> (U_2_bool (MapType0Select b@@32 o@@37)) (U_2_bool (MapType0Select a@@40 o@@37)))))
 :qid |DafnyPre.750:32|
 :skolemid |481|
 :pattern ( (MapType0Select a@@40 o@@37))
 :pattern ( (MapType0Select b@@32 o@@37))
)) (|ISet#Equal| a@@40 b@@32)))))
 :qid |DafnyPre.749:17|
 :skolemid |482|
 :pattern ( (|ISet#Equal| a@@40 b@@32))
)))
(assert (forall ((a@@41 T@U) (b@@33 T@U) ) (! (let ((T@@59 (MapType0TypeInv0 (type a@@41))))
 (=> (and (and (= (type a@@41) (MapType0Type T@@59 boolType)) (= (type b@@33) (MapType0Type T@@59 boolType))) (|ISet#Equal| a@@41 b@@33)) (= a@@41 b@@33)))
 :qid |DafnyPre.751:17|
 :skolemid |483|
 :pattern ( (|ISet#Equal| a@@41 b@@33))
)))
(assert (forall ((a@@42 T@U) (b@@34 T@U) ) (! (let ((T@@60 (MapType0TypeInv0 (type a@@42))))
 (=> (and (= (type a@@42) (MapType0Type T@@60 boolType)) (= (type b@@34) (MapType0Type T@@60 boolType))) (and (=> (|ISet#Disjoint| a@@42 b@@34) (forall ((o@@38 T@U) ) (!  (=> (= (type o@@38) T@@60) (or (not (U_2_bool (MapType0Select a@@42 o@@38))) (not (U_2_bool (MapType0Select b@@34 o@@38)))))
 :qid |DafnyPre.756:35|
 :skolemid |484|
 :pattern ( (MapType0Select a@@42 o@@38))
 :pattern ( (MapType0Select b@@34 o@@38))
))) (=> (forall ((o@@39 T@U) ) (!  (=> (= (type o@@39) T@@60) (or (not (U_2_bool (MapType0Select a@@42 o@@39))) (not (U_2_bool (MapType0Select b@@34 o@@39)))))
 :qid |DafnyPre.756:35|
 :skolemid |484|
 :pattern ( (MapType0Select a@@42 o@@39))
 :pattern ( (MapType0Select b@@34 o@@39))
)) (|ISet#Disjoint| a@@42 b@@34)))))
 :qid |DafnyPre.755:18|
 :skolemid |485|
 :pattern ( (|ISet#Disjoint| a@@42 b@@34))
)))
(assert (forall ((a@@43 Int) (b@@35 Int) ) (!  (and (=> (<= a@@43 b@@35) (= (|Math#min| a@@43 b@@35) a@@43)) (=> (= (|Math#min| a@@43 b@@35) a@@43) (<= a@@43 b@@35)))
 :qid |DafnyPre.763:15|
 :skolemid |486|
 :pattern ( (|Math#min| a@@43 b@@35))
)))
(assert (forall ((a@@44 Int) (b@@36 Int) ) (!  (and (=> (<= b@@36 a@@44) (= (|Math#min| a@@44 b@@36) b@@36)) (=> (= (|Math#min| a@@44 b@@36) b@@36) (<= b@@36 a@@44)))
 :qid |DafnyPre.764:15|
 :skolemid |487|
 :pattern ( (|Math#min| a@@44 b@@36))
)))
(assert (forall ((a@@45 Int) (b@@37 Int) ) (!  (or (= (|Math#min| a@@45 b@@37) a@@45) (= (|Math#min| a@@45 b@@37) b@@37))
 :qid |DafnyPre.765:15|
 :skolemid |488|
 :pattern ( (|Math#min| a@@45 b@@37))
)))
(assert (forall ((a@@46 Int) ) (!  (=> (<= 0 a@@46) (= (|Math#clip| a@@46) a@@46))
 :qid |DafnyPre.768:15|
 :skolemid |489|
 :pattern ( (|Math#clip| a@@46))
)))
(assert (forall ((a@@47 Int) ) (!  (=> (< a@@47 0) (= (|Math#clip| a@@47) 0))
 :qid |DafnyPre.769:15|
 :skolemid |490|
 :pattern ( (|Math#clip| a@@47))
)))
(assert (forall ((ms T@U) ) (! (let ((T@@61 (MapType0TypeInv0 (type ms))))
 (=> (= (type ms) (MapType0Type T@@61 intType)) (and (=> ($IsGoodMultiSet ms) (forall ((bx@@31 T@U) ) (!  (=> (= (type bx@@31) T@@61) (and (<= 0 (U_2_int (MapType0Select ms bx@@31))) (<= (U_2_int (MapType0Select ms bx@@31)) (|MultiSet#Card| ms))))
 :qid |DafnyPre.777:11|
 :skolemid |491|
 :pattern ( (MapType0Select ms bx@@31))
))) (=> (forall ((bx@@32 T@U) ) (!  (=> (= (type bx@@32) T@@61) (and (<= 0 (U_2_int (MapType0Select ms bx@@32))) (<= (U_2_int (MapType0Select ms bx@@32)) (|MultiSet#Card| ms))))
 :qid |DafnyPre.777:11|
 :skolemid |491|
 :pattern ( (MapType0Select ms bx@@32))
)) ($IsGoodMultiSet ms)))))
 :qid |DafnyPre.775:18|
 :skolemid |492|
 :pattern ( ($IsGoodMultiSet ms))
)))
(assert (forall ((s@@5 T@U) ) (! (let ((T@@62 (MapType0TypeInv0 (type s@@5))))
 (=> (= (type s@@5) (MapType0Type T@@62 intType)) (<= 0 (|MultiSet#Card| s@@5))))
 :qid |DafnyPre.780:18|
 :skolemid |493|
 :pattern ( (|MultiSet#Card| s@@5))
)))
(assert (forall ((s@@6 T@U) (x@@27 T@U) (n@@5 T@U) ) (! (let ((T@@63 (type x@@27)))
 (=> (and (and (= (type s@@6) (MapType0Type T@@63 intType)) (= (type n@@5) intType)) (<= 0 (U_2_int n@@5))) (= (|MultiSet#Card| (MapType0Store s@@6 x@@27 n@@5)) (+ (- (|MultiSet#Card| s@@6) (U_2_int (MapType0Select s@@6 x@@27))) (U_2_int n@@5)))))
 :qid |DafnyPre.781:18|
 :skolemid |494|
 :pattern ( (|MultiSet#Card| (MapType0Store s@@6 x@@27 n@@5)))
)))
(assert (forall ((T@@64 T@T) ) (! (= (type (|MultiSet#Empty| T@@64)) (MapType0Type T@@64 intType))
 :qid |funType:MultiSet#Empty|
 :pattern ( (|MultiSet#Empty| T@@64))
)))
(assert (forall ((o@@40 T@U) ) (! (let ((T@@65 (type o@@40)))
(= (U_2_int (MapType0Select (|MultiSet#Empty| T@@65) o@@40)) 0))
 :qid |DafnyPre.785:18|
 :skolemid |495|
 :pattern ( (let ((T@@65 (type o@@40)))
(MapType0Select (|MultiSet#Empty| T@@65) o@@40)))
)))
(assert (forall ((s@@7 T@U) ) (! (let ((T@@66 (MapType0TypeInv0 (type s@@7))))
 (=> (= (type s@@7) (MapType0Type T@@66 intType)) (and (and (=> (= (|MultiSet#Card| s@@7) 0) (= s@@7 (|MultiSet#Empty| T@@66))) (=> (= s@@7 (|MultiSet#Empty| T@@66)) (= (|MultiSet#Card| s@@7) 0))) (=> (not (= (|MultiSet#Card| s@@7) 0)) (exists ((x@@28 T@U) ) (!  (and (= (type x@@28) T@@66) (< 0 (U_2_int (MapType0Select s@@7 x@@28))))
 :qid |DafnyPre.788:38|
 :skolemid |496|
 :no-pattern (type x@@28)
 :no-pattern (U_2_int x@@28)
 :no-pattern (U_2_bool x@@28)
))))))
 :qid |DafnyPre.786:18|
 :skolemid |497|
 :pattern ( (|MultiSet#Card| s@@7))
)))
(assert (forall ((arg0@@79 T@U) ) (! (let ((T@@67 (type arg0@@79)))
(= (type (|MultiSet#Singleton| arg0@@79)) (MapType0Type T@@67 intType)))
 :qid |funType:MultiSet#Singleton|
 :pattern ( (|MultiSet#Singleton| arg0@@79))
)))
(assert (forall ((r@@4 T@U) (o@@41 T@U) ) (! (let ((T@@68 (type r@@4)))
 (=> (= (type o@@41) T@@68) (and (and (=> (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@41)) 1) (= r@@4 o@@41)) (=> (= r@@4 o@@41) (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@41)) 1))) (and (=> (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@41)) 0) (not (= r@@4 o@@41))) (=> (not (= r@@4 o@@41)) (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@41)) 0))))))
 :qid |DafnyPre.791:18|
 :skolemid |498|
 :pattern ( (MapType0Select (|MultiSet#Singleton| r@@4) o@@41))
)))
(assert (forall ((arg0@@80 T@U) (arg1@@31 T@U) ) (! (let ((T@@69 (type arg1@@31)))
(= (type (|MultiSet#UnionOne| arg0@@80 arg1@@31)) (MapType0Type T@@69 intType)))
 :qid |funType:MultiSet#UnionOne|
 :pattern ( (|MultiSet#UnionOne| arg0@@80 arg1@@31))
)))
(assert (forall ((r@@5 T@U) ) (! (let ((T@@70 (type r@@5)))
(= (|MultiSet#Singleton| r@@5) (|MultiSet#UnionOne| (|MultiSet#Empty| T@@70) r@@5)))
 :qid |DafnyPre.793:18|
 :skolemid |499|
 :pattern ( (|MultiSet#Singleton| r@@5))
)))
(assert (forall ((a@@48 T@U) (x@@29 T@U) (o@@42 T@U) ) (! (let ((T@@71 (type x@@29)))
 (=> (and (= (type a@@48) (MapType0Type T@@71 intType)) (= (type o@@42) T@@71)) (and (=> (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@48 x@@29) o@@42))) (or (= o@@42 x@@29) (< 0 (U_2_int (MapType0Select a@@48 o@@42))))) (=> (or (= o@@42 x@@29) (< 0 (U_2_int (MapType0Select a@@48 o@@42)))) (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@48 x@@29) o@@42)))))))
 :qid |DafnyPre.797:18|
 :skolemid |500|
 :pattern ( (MapType0Select (|MultiSet#UnionOne| a@@48 x@@29) o@@42))
)))
(assert (forall ((a@@49 T@U) (x@@30 T@U) ) (! (let ((T@@72 (type x@@30)))
 (=> (= (type a@@49) (MapType0Type T@@72 intType)) (= (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@49 x@@30) x@@30)) (+ (U_2_int (MapType0Select a@@49 x@@30)) 1))))
 :qid |DafnyPre.800:18|
 :skolemid |501|
 :pattern ( (|MultiSet#UnionOne| a@@49 x@@30))
)))
(assert (forall ((a@@50 T@U) (x@@31 T@U) (y@@9 T@U) ) (! (let ((T@@73 (type x@@31)))
 (=> (and (and (= (type a@@50) (MapType0Type T@@73 intType)) (= (type y@@9) T@@73)) (< 0 (U_2_int (MapType0Select a@@50 y@@9)))) (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@50 x@@31) y@@9)))))
 :qid |DafnyPre.803:18|
 :skolemid |502|
 :pattern ( (|MultiSet#UnionOne| a@@50 x@@31) (MapType0Select a@@50 y@@9))
)))
(assert (forall ((a@@51 T@U) (x@@32 T@U) (y@@10 T@U) ) (! (let ((T@@74 (type x@@32)))
 (=> (and (and (= (type a@@51) (MapType0Type T@@74 intType)) (= (type y@@10) T@@74)) (not (= x@@32 y@@10))) (= (U_2_int (MapType0Select a@@51 y@@10)) (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@51 x@@32) y@@10)))))
 :qid |DafnyPre.806:18|
 :skolemid |503|
 :pattern ( (|MultiSet#UnionOne| a@@51 x@@32) (MapType0Select a@@51 y@@10))
)))
(assert (forall ((a@@52 T@U) (x@@33 T@U) ) (! (let ((T@@75 (type x@@33)))
 (=> (= (type a@@52) (MapType0Type T@@75 intType)) (= (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@33)) (+ (|MultiSet#Card| a@@52) 1))))
 :qid |DafnyPre.808:18|
 :skolemid |504|
 :pattern ( (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@33)))
)))
(assert (forall ((arg0@@81 T@U) (arg1@@32 T@U) ) (! (let ((T@@76 (MapType0TypeInv0 (type arg0@@81))))
(= (type (|MultiSet#Union| arg0@@81 arg1@@32)) (MapType0Type T@@76 intType)))
 :qid |funType:MultiSet#Union|
 :pattern ( (|MultiSet#Union| arg0@@81 arg1@@32))
)))
(assert (forall ((a@@53 T@U) (b@@38 T@U) (o@@43 T@U) ) (! (let ((T@@77 (type o@@43)))
 (=> (and (= (type a@@53) (MapType0Type T@@77 intType)) (= (type b@@38) (MapType0Type T@@77 intType))) (= (U_2_int (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@43)) (+ (U_2_int (MapType0Select a@@53 o@@43)) (U_2_int (MapType0Select b@@38 o@@43))))))
 :qid |DafnyPre.814:18|
 :skolemid |505|
 :pattern ( (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@43))
)))
(assert (forall ((a@@54 T@U) (b@@39 T@U) ) (! (let ((T@@78 (MapType0TypeInv0 (type a@@54))))
 (=> (and (= (type a@@54) (MapType0Type T@@78 intType)) (= (type b@@39) (MapType0Type T@@78 intType))) (= (|MultiSet#Card| (|MultiSet#Union| a@@54 b@@39)) (+ (|MultiSet#Card| a@@54) (|MultiSet#Card| b@@39)))))
 :qid |DafnyPre.816:18|
 :skolemid |506|
 :pattern ( (|MultiSet#Card| (|MultiSet#Union| a@@54 b@@39)))
)))
(assert (forall ((arg0@@82 T@U) (arg1@@33 T@U) ) (! (let ((T@@79 (MapType0TypeInv0 (type arg0@@82))))
(= (type (|MultiSet#Intersection| arg0@@82 arg1@@33)) (MapType0Type T@@79 intType)))
 :qid |funType:MultiSet#Intersection|
 :pattern ( (|MultiSet#Intersection| arg0@@82 arg1@@33))
)))
(assert (forall ((a@@55 T@U) (b@@40 T@U) (o@@44 T@U) ) (! (let ((T@@80 (type o@@44)))
 (=> (and (= (type a@@55) (MapType0Type T@@80 intType)) (= (type b@@40) (MapType0Type T@@80 intType))) (= (U_2_int (MapType0Select (|MultiSet#Intersection| a@@55 b@@40) o@@44)) (|Math#min| (U_2_int (MapType0Select a@@55 o@@44)) (U_2_int (MapType0Select b@@40 o@@44))))))
 :qid |DafnyPre.820:18|
 :skolemid |507|
 :pattern ( (MapType0Select (|MultiSet#Intersection| a@@55 b@@40) o@@44))
)))
(assert (forall ((a@@56 T@U) (b@@41 T@U) ) (! (let ((T@@81 (MapType0TypeInv0 (type a@@56))))
 (=> (and (= (type a@@56) (MapType0Type T@@81 intType)) (= (type b@@41) (MapType0Type T@@81 intType))) (= (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41) (|MultiSet#Intersection| a@@56 b@@41))))
 :qid |DafnyPre.824:18|
 :skolemid |508|
 :pattern ( (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41))
)))
(assert (forall ((a@@57 T@U) (b@@42 T@U) ) (! (let ((T@@82 (MapType0TypeInv0 (type a@@57))))
 (=> (and (= (type a@@57) (MapType0Type T@@82 intType)) (= (type b@@42) (MapType0Type T@@82 intType))) (= (|MultiSet#Intersection| a@@57 (|MultiSet#Intersection| a@@57 b@@42)) (|MultiSet#Intersection| a@@57 b@@42))))
 :qid |DafnyPre.826:18|
 :skolemid |509|
 :pattern ( (|MultiSet#Intersection| a@@57 (|MultiSet#Intersection| a@@57 b@@42)))
)))
(assert (forall ((arg0@@83 T@U) (arg1@@34 T@U) ) (! (let ((T@@83 (MapType0TypeInv0 (type arg0@@83))))
(= (type (|MultiSet#Difference| arg0@@83 arg1@@34)) (MapType0Type T@@83 intType)))
 :qid |funType:MultiSet#Difference|
 :pattern ( (|MultiSet#Difference| arg0@@83 arg1@@34))
)))
(assert (forall ((a@@58 T@U) (b@@43 T@U) (o@@45 T@U) ) (! (let ((T@@84 (type o@@45)))
 (=> (and (= (type a@@58) (MapType0Type T@@84 intType)) (= (type b@@43) (MapType0Type T@@84 intType))) (= (U_2_int (MapType0Select (|MultiSet#Difference| a@@58 b@@43) o@@45)) (|Math#clip| (- (U_2_int (MapType0Select a@@58 o@@45)) (U_2_int (MapType0Select b@@43 o@@45)))))))
 :qid |DafnyPre.831:18|
 :skolemid |510|
 :pattern ( (MapType0Select (|MultiSet#Difference| a@@58 b@@43) o@@45))
)))
(assert (forall ((a@@59 T@U) (b@@44 T@U) (y@@11 T@U) ) (! (let ((T@@85 (type y@@11)))
 (=> (and (and (= (type a@@59) (MapType0Type T@@85 intType)) (= (type b@@44) (MapType0Type T@@85 intType))) (<= (U_2_int (MapType0Select a@@59 y@@11)) (U_2_int (MapType0Select b@@44 y@@11)))) (= (U_2_int (MapType0Select (|MultiSet#Difference| a@@59 b@@44) y@@11)) 0)))
 :qid |DafnyPre.833:18|
 :skolemid |511|
 :pattern ( (|MultiSet#Difference| a@@59 b@@44) (MapType0Select b@@44 y@@11) (MapType0Select a@@59 y@@11))
)))
(assert (forall ((a@@60 T@U) (b@@45 T@U) ) (! (let ((T@@86 (MapType0TypeInv0 (type a@@60))))
 (=> (and (= (type a@@60) (MapType0Type T@@86 intType)) (= (type b@@45) (MapType0Type T@@86 intType))) (and (= (+ (+ (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (|MultiSet#Card| (|MultiSet#Difference| b@@45 a@@60))) (* 2 (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))) (|MultiSet#Card| (|MultiSet#Union| a@@60 b@@45))) (= (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (- (|MultiSet#Card| a@@60) (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))))))
 :qid |DafnyPre.835:18|
 :skolemid |512|
 :pattern ( (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)))
)))
(assert (forall ((a@@61 T@U) (b@@46 T@U) ) (! (let ((T@@87 (MapType0TypeInv0 (type a@@61))))
 (=> (and (= (type a@@61) (MapType0Type T@@87 intType)) (= (type b@@46) (MapType0Type T@@87 intType))) (and (=> (|MultiSet#Subset| a@@61 b@@46) (forall ((o@@46 T@U) ) (!  (=> (= (type o@@46) T@@87) (<= (U_2_int (MapType0Select a@@61 o@@46)) (U_2_int (MapType0Select b@@46 o@@46))))
 :qid |DafnyPre.845:37|
 :skolemid |513|
 :pattern ( (MapType0Select a@@61 o@@46))
 :pattern ( (MapType0Select b@@46 o@@46))
))) (=> (forall ((o@@47 T@U) ) (!  (=> (= (type o@@47) T@@87) (<= (U_2_int (MapType0Select a@@61 o@@47)) (U_2_int (MapType0Select b@@46 o@@47))))
 :qid |DafnyPre.845:37|
 :skolemid |513|
 :pattern ( (MapType0Select a@@61 o@@47))
 :pattern ( (MapType0Select b@@46 o@@47))
)) (|MultiSet#Subset| a@@61 b@@46)))))
 :qid |DafnyPre.844:17|
 :skolemid |514|
 :pattern ( (|MultiSet#Subset| a@@61 b@@46))
)))
(assert (forall ((a@@62 T@U) (b@@47 T@U) ) (! (let ((T@@88 (MapType0TypeInv0 (type a@@62))))
 (=> (and (= (type a@@62) (MapType0Type T@@88 intType)) (= (type b@@47) (MapType0Type T@@88 intType))) (and (=> (|MultiSet#Equal| a@@62 b@@47) (forall ((o@@48 T@U) ) (!  (=> (= (type o@@48) T@@88) (= (U_2_int (MapType0Select a@@62 o@@48)) (U_2_int (MapType0Select b@@47 o@@48))))
 :qid |DafnyPre.849:36|
 :skolemid |515|
 :pattern ( (MapType0Select a@@62 o@@48))
 :pattern ( (MapType0Select b@@47 o@@48))
))) (=> (forall ((o@@49 T@U) ) (!  (=> (= (type o@@49) T@@88) (= (U_2_int (MapType0Select a@@62 o@@49)) (U_2_int (MapType0Select b@@47 o@@49))))
 :qid |DafnyPre.849:36|
 :skolemid |515|
 :pattern ( (MapType0Select a@@62 o@@49))
 :pattern ( (MapType0Select b@@47 o@@49))
)) (|MultiSet#Equal| a@@62 b@@47)))))
 :qid |DafnyPre.848:17|
 :skolemid |516|
 :pattern ( (|MultiSet#Equal| a@@62 b@@47))
)))
(assert (forall ((a@@63 T@U) (b@@48 T@U) ) (! (let ((T@@89 (MapType0TypeInv0 (type a@@63))))
 (=> (and (and (= (type a@@63) (MapType0Type T@@89 intType)) (= (type b@@48) (MapType0Type T@@89 intType))) (|MultiSet#Equal| a@@63 b@@48)) (= a@@63 b@@48)))
 :qid |DafnyPre.851:17|
 :skolemid |517|
 :pattern ( (|MultiSet#Equal| a@@63 b@@48))
)))
(assert (forall ((a@@64 T@U) (b@@49 T@U) ) (! (let ((T@@90 (MapType0TypeInv0 (type a@@64))))
 (=> (and (= (type a@@64) (MapType0Type T@@90 intType)) (= (type b@@49) (MapType0Type T@@90 intType))) (and (=> (|MultiSet#Disjoint| a@@64 b@@49) (forall ((o@@50 T@U) ) (!  (=> (= (type o@@50) T@@90) (or (= (U_2_int (MapType0Select a@@64 o@@50)) 0) (= (U_2_int (MapType0Select b@@49 o@@50)) 0)))
 :qid |DafnyPre.856:39|
 :skolemid |518|
 :pattern ( (MapType0Select a@@64 o@@50))
 :pattern ( (MapType0Select b@@49 o@@50))
))) (=> (forall ((o@@51 T@U) ) (!  (=> (= (type o@@51) T@@90) (or (= (U_2_int (MapType0Select a@@64 o@@51)) 0) (= (U_2_int (MapType0Select b@@49 o@@51)) 0)))
 :qid |DafnyPre.856:39|
 :skolemid |518|
 :pattern ( (MapType0Select a@@64 o@@51))
 :pattern ( (MapType0Select b@@49 o@@51))
)) (|MultiSet#Disjoint| a@@64 b@@49)))))
 :qid |DafnyPre.855:18|
 :skolemid |519|
 :pattern ( (|MultiSet#Disjoint| a@@64 b@@49))
)))
(assert (forall ((arg0@@84 T@U) ) (! (let ((T@@91 (MapType0TypeInv0 (type arg0@@84))))
(= (type (|MultiSet#FromSet| arg0@@84)) (MapType0Type T@@91 intType)))
 :qid |funType:MultiSet#FromSet|
 :pattern ( (|MultiSet#FromSet| arg0@@84))
)))
(assert (forall ((s@@8 T@U) (a@@65 T@U) ) (! (let ((T@@92 (type a@@65)))
 (=> (= (type s@@8) (MapType0Type T@@92 boolType)) (and (and (=> (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 0) (not (U_2_bool (MapType0Select s@@8 a@@65)))) (=> (not (U_2_bool (MapType0Select s@@8 a@@65))) (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 0))) (and (=> (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 1) (U_2_bool (MapType0Select s@@8 a@@65))) (=> (U_2_bool (MapType0Select s@@8 a@@65)) (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 1))))))
 :qid |DafnyPre.860:18|
 :skolemid |520|
 :pattern ( (MapType0Select (|MultiSet#FromSet| s@@8) a@@65))
)))
(assert (forall ((s@@9 T@U) ) (! (let ((T@@93 (MapType0TypeInv0 (type s@@9))))
 (=> (= (type s@@9) (MapType0Type T@@93 boolType)) (= (|MultiSet#Card| (|MultiSet#FromSet| s@@9)) (|Set#Card| s@@9))))
 :qid |DafnyPre.863:18|
 :skolemid |521|
 :pattern ( (|MultiSet#Card| (|MultiSet#FromSet| s@@9)))
)))
(assert (forall ((arg0@@85 T@U) ) (! (let ((T@@94 (SeqTypeInv0 (type arg0@@85))))
(= (type (|MultiSet#FromSeq| arg0@@85)) (MapType0Type T@@94 intType)))
 :qid |funType:MultiSet#FromSeq|
 :pattern ( (|MultiSet#FromSeq| arg0@@85))
)))
(assert (forall ((s@@10 T@U) ) (! (let ((T@@95 (SeqTypeInv0 (type s@@10))))
 (=> (= (type s@@10) (SeqType T@@95)) ($IsGoodMultiSet (|MultiSet#FromSeq| s@@10))))
 :qid |DafnyPre.869:18|
 :skolemid |522|
 :pattern ( (|MultiSet#FromSeq| s@@10))
)))
(assert (forall ((s@@11 T@U) ) (! (let ((T@@96 (SeqTypeInv0 (type s@@11))))
 (=> (= (type s@@11) (SeqType T@@96)) (= (|MultiSet#Card| (|MultiSet#FromSeq| s@@11)) (|Seq#Length| s@@11))))
 :qid |DafnyPre.871:18|
 :skolemid |523|
 :pattern ( (|MultiSet#Card| (|MultiSet#FromSeq| s@@11)))
)))
(assert (forall ((arg0@@86 T@U) (arg1@@35 T@U) ) (! (let ((T@@97 (type arg1@@35)))
(= (type (|Seq#Build| arg0@@86 arg1@@35)) (SeqType T@@97)))
 :qid |funType:Seq#Build|
 :pattern ( (|Seq#Build| arg0@@86 arg1@@35))
)))
(assert (forall ((s@@12 T@U) (v@@25 T@U) ) (! (let ((T@@98 (type v@@25)))
 (=> (= (type s@@12) (SeqType T@@98)) (= (|MultiSet#FromSeq| (|Seq#Build| s@@12 v@@25)) (|MultiSet#UnionOne| (|MultiSet#FromSeq| s@@12) v@@25))))
 :qid |DafnyPre.875:18|
 :skolemid |524|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Build| s@@12 v@@25)))
)))
(assert (forall ((T@@99 T@T) ) (! (= (type (|Seq#Empty| T@@99)) (SeqType T@@99))
 :qid |funType:Seq#Empty|
 :pattern ( (|Seq#Empty| T@@99))
)))
(assert (forall ((T@@100 T@T) ) (! (= (|MultiSet#FromSeq| (|Seq#Empty| T@@100)) (|MultiSet#Empty| T@@100))
 :skolemid |525|
)))
(assert (forall ((arg0@@87 T@U) (arg1@@36 T@U) ) (! (let ((T@@101 (SeqTypeInv0 (type arg0@@87))))
(= (type (|Seq#Append| arg0@@87 arg1@@36)) (SeqType T@@101)))
 :qid |funType:Seq#Append|
 :pattern ( (|Seq#Append| arg0@@87 arg1@@36))
)))
(assert (forall ((a@@66 T@U) (b@@50 T@U) ) (! (let ((T@@102 (SeqTypeInv0 (type a@@66))))
 (=> (and (= (type a@@66) (SeqType T@@102)) (= (type b@@50) (SeqType T@@102))) (= (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)) (|MultiSet#Union| (|MultiSet#FromSeq| a@@66) (|MultiSet#FromSeq| b@@50)))))
 :qid |DafnyPre.882:18|
 :skolemid |526|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)))
)))
(assert (forall ((arg0@@88 T@U) (arg1@@37 Int) (arg2@@1 T@U) ) (! (let ((T@@103 (type arg2@@1)))
(= (type (|Seq#Update| arg0@@88 arg1@@37 arg2@@1)) (SeqType T@@103)))
 :qid |funType:Seq#Update|
 :pattern ( (|Seq#Update| arg0@@88 arg1@@37 arg2@@1))
)))
(assert (forall ((s@@13 T@U) (i@@8 Int) (v@@26 T@U) (x@@34 T@U) ) (! (let ((T@@104 (type v@@26)))
 (=> (and (and (= (type s@@13) (SeqType T@@104)) (= (type x@@34) T@@104)) (and (<= 0 i@@8) (< i@@8 (|Seq#Length| s@@13)))) (= (U_2_int (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@8 v@@26)) x@@34)) (U_2_int (MapType0Select (|MultiSet#Union| (|MultiSet#Difference| (|MultiSet#FromSeq| s@@13) (|MultiSet#Singleton| (|Seq#Index| s@@13 i@@8))) (|MultiSet#Singleton| v@@26)) x@@34)))))
 :qid |DafnyPre.887:18|
 :skolemid |527|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@8 v@@26)) x@@34))
)))
(assert (forall ((s@@14 T@U) (x@@35 T@U) ) (! (let ((T@@105 (type x@@35)))
 (=> (= (type s@@14) (SeqType T@@105)) (and (=> (exists ((i@@9 Int) ) (!  (and (and (<= 0 i@@9) (< i@@9 (|Seq#Length| s@@14))) (= x@@35 (|Seq#Index| s@@14 i@@9)))
 :qid |DafnyPre.894:11|
 :skolemid |528|
 :pattern ( (|Seq#Index| s@@14 i@@9))
)) (< 0 (U_2_int (MapType0Select (|MultiSet#FromSeq| s@@14) x@@35)))) (=> (< 0 (U_2_int (MapType0Select (|MultiSet#FromSeq| s@@14) x@@35))) (exists ((i@@10 Int) ) (!  (and (and (<= 0 i@@10) (< i@@10 (|Seq#Length| s@@14))) (= x@@35 (|Seq#Index| s@@14 i@@10)))
 :qid |DafnyPre.894:11|
 :skolemid |528|
 :pattern ( (|Seq#Index| s@@14 i@@10))
))))))
 :qid |DafnyPre.893:18|
 :skolemid |529|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| s@@14) x@@35))
)))
(assert (forall ((s@@15 T@U) ) (! (let ((T@@106 (SeqTypeInv0 (type s@@15))))
 (=> (= (type s@@15) (SeqType T@@106)) (<= 0 (|Seq#Length| s@@15))))
 :qid |DafnyPre.903:18|
 :skolemid |530|
 :pattern ( (|Seq#Length| s@@15))
)))
(assert (forall ((T@@107 T@T) ) (! (= (|Seq#Length| (|Seq#Empty| T@@107)) 0)
 :skolemid |531|
 :pattern ( (|Seq#Empty| T@@107))
)))
(assert (forall ((s@@16 T@U) ) (! (let ((T@@108 (SeqTypeInv0 (type s@@16))))
 (=> (and (= (type s@@16) (SeqType T@@108)) (= (|Seq#Length| s@@16) 0)) (= s@@16 (|Seq#Empty| T@@108))))
 :qid |DafnyPre.907:18|
 :skolemid |532|
 :pattern ( (|Seq#Length| s@@16))
)))
(assert (forall ((t@@23 T@U) (T@@109 T@T) ) (!  (=> (= (type t@@23) TyType) ($Is (|Seq#Empty| T@@109) t@@23))
 :qid |DafnyPre.917:18|
 :skolemid |533|
 :pattern ( ($Is (|Seq#Empty| T@@109) t@@23))
)))
(assert (forall ((arg0@@89 T@U) ) (! (let ((T@@110 (type arg0@@89)))
(= (type (|Seq#Singleton| arg0@@89)) (SeqType T@@110)))
 :qid |funType:Seq#Singleton|
 :pattern ( (|Seq#Singleton| arg0@@89))
)))
(assert (forall ((t@@24 T@U) ) (! (= (|Seq#Length| (|Seq#Singleton| t@@24)) 1)
 :qid |DafnyPre.920:18|
 :skolemid |534|
 :pattern ( (|Seq#Length| (|Seq#Singleton| t@@24)))
)))
(assert  (and (forall ((arg0@@90 T@U) ) (! (let ((T@@111 (SeqTypeInv0 (type arg0@@90))))
(= (type (|Seq#Build_inv0| arg0@@90)) (SeqType T@@111)))
 :qid |funType:Seq#Build_inv0|
 :pattern ( (|Seq#Build_inv0| arg0@@90))
)) (forall ((arg0@@91 T@U) ) (! (let ((T@@112 (SeqTypeInv0 (type arg0@@91))))
(= (type (|Seq#Build_inv1| arg0@@91)) T@@112))
 :qid |funType:Seq#Build_inv1|
 :pattern ( (|Seq#Build_inv1| arg0@@91))
))))
(assert (forall ((s@@17 T@U) (val@@5 T@U) ) (! (let ((T@@113 (type val@@5)))
 (=> (= (type s@@17) (SeqType T@@113)) (and (= (|Seq#Build_inv0| (|Seq#Build| s@@17 val@@5)) s@@17) (= (|Seq#Build_inv1| (|Seq#Build| s@@17 val@@5)) val@@5))))
 :qid |DafnyPre.925:18|
 :skolemid |535|
 :pattern ( (|Seq#Build| s@@17 val@@5))
)))
(assert (forall ((s@@18 T@U) (v@@27 T@U) ) (! (let ((T@@114 (type v@@27)))
 (=> (= (type s@@18) (SeqType T@@114)) (= (|Seq#Length| (|Seq#Build| s@@18 v@@27)) (+ 1 (|Seq#Length| s@@18)))))
 :qid |DafnyPre.930:18|
 :skolemid |536|
 :pattern ( (|Seq#Build| s@@18 v@@27))
)))
(assert (forall ((s@@19 T@U) (i@@11 Int) (v@@28 T@U) ) (! (let ((T@@115 (type v@@28)))
 (=> (= (type s@@19) (SeqType T@@115)) (and (=> (= i@@11 (|Seq#Length| s@@19)) (= (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11) v@@28)) (=> (not (= i@@11 (|Seq#Length| s@@19))) (= (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11) (|Seq#Index| s@@19 i@@11))))))
 :qid |DafnyPre.933:18|
 :skolemid |537|
 :pattern ( (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11))
)))
(assert (forall ((s@@20 T@U) (bx@@33 T@U) (t@@25 T@U) ) (!  (=> (and (and (and (= (type s@@20) (SeqType BoxType)) (= (type bx@@33) BoxType)) (= (type t@@25) TyType)) (and ($Is s@@20 (TSeq t@@25)) ($IsBox bx@@33 t@@25))) ($Is (|Seq#Build| s@@20 bx@@33) (TSeq t@@25)))
 :qid |DafnyPre.938:15|
 :skolemid |538|
 :pattern ( ($Is (|Seq#Build| s@@20 bx@@33) (TSeq t@@25)))
)))
(assert  (and (= (Ctor HandleTypeType) 22) (forall ((arg0@@92 T@U) (arg1@@38 T@U) (arg2@@2 Int) (arg3 T@U) ) (! (= (type (|Seq#Create| arg0@@92 arg1@@38 arg2@@2 arg3)) (SeqType BoxType))
 :qid |funType:Seq#Create|
 :pattern ( (|Seq#Create| arg0@@92 arg1@@38 arg2@@2 arg3))
))))
(assert (forall ((ty T@U) (heap T@U) (len Int) (init T@U) ) (!  (=> (and (and (and (= (type ty) TyType) (= (type heap) (MapType0Type refType MapType1Type))) (= (type init) HandleTypeType)) (and ($IsGoodHeap heap) (<= 0 len))) (= (|Seq#Length| (|Seq#Create| ty heap len init)) len))
 :qid |DafnyPre.942:15|
 :skolemid |539|
 :pattern ( (|Seq#Length| (|Seq#Create| ty heap len init)))
)))
(assert (forall ((arg0@@93 T@U) (arg1@@39 T@U) (arg2@@3 T@U) (arg3@@0 T@U) (arg4 T@U) ) (! (= (type (Apply1 arg0@@93 arg1@@39 arg2@@3 arg3@@0 arg4)) BoxType)
 :qid |funType:Apply1|
 :pattern ( (Apply1 arg0@@93 arg1@@39 arg2@@3 arg3@@0 arg4))
)))
(assert (forall ((ty@@0 T@U) (heap@@0 T@U) (len@@0 Int) (init@@0 T@U) (i@@12 Int) ) (!  (=> (and (and (and (= (type ty@@0) TyType) (= (type heap@@0) (MapType0Type refType MapType1Type))) (= (type init@@0) HandleTypeType)) (and (and ($IsGoodHeap heap@@0) (<= 0 i@@12)) (< i@@12 len@@0))) (= (|Seq#Index| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@12) (Apply1 TInt (TSeq ty@@0) heap@@0 init@@0 ($Box (int_2_U i@@12)))))
 :qid |DafnyPre.946:15|
 :skolemid |540|
 :pattern ( (|Seq#Index| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@12))
)))
(assert (forall ((s0 T@U) (s1 T@U) ) (! (let ((T@@116 (SeqTypeInv0 (type s0))))
 (=> (and (= (type s0) (SeqType T@@116)) (= (type s1) (SeqType T@@116))) (= (|Seq#Length| (|Seq#Append| s0 s1)) (+ (|Seq#Length| s0) (|Seq#Length| s1)))))
 :qid |DafnyPre.952:18|
 :skolemid |541|
 :pattern ( (|Seq#Length| (|Seq#Append| s0 s1)))
)))
(assert (forall ((s0@@0 T@U) (s1@@0 T@U) (t@@26 T@U) ) (!  (=> (and (and (and (= (type s0@@0) (SeqType BoxType)) (= (type s1@@0) (SeqType BoxType))) (= (type t@@26) TyType)) (and ($Is s0@@0 t@@26) ($Is s1@@0 t@@26))) ($Is (|Seq#Append| s0@@0 s1@@0) t@@26))
 :qid |DafnyPre.956:15|
 :skolemid |542|
 :pattern ( ($Is (|Seq#Append| s0@@0 s1@@0) t@@26))
)))
(assert (forall ((t@@27 T@U) ) (! (= (|Seq#Index| (|Seq#Singleton| t@@27) 0) t@@27)
 :qid |DafnyPre.960:18|
 :skolemid |543|
 :pattern ( (|Seq#Index| (|Seq#Singleton| t@@27) 0))
)))
(assert (forall ((s0@@1 T@U) (s1@@1 T@U) (n@@6 Int) ) (! (let ((T@@117 (SeqTypeInv0 (type s0@@1))))
 (=> (and (= (type s0@@1) (SeqType T@@117)) (= (type s1@@1) (SeqType T@@117))) (and (=> (< n@@6 (|Seq#Length| s0@@1)) (= (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6) (|Seq#Index| s0@@1 n@@6))) (=> (<= (|Seq#Length| s0@@1) n@@6) (= (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6) (|Seq#Index| s1@@1 (- n@@6 (|Seq#Length| s0@@1))))))))
 :qid |DafnyPre.961:18|
 :skolemid |544|
 :pattern ( (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6))
)))
(assert (forall ((s@@21 T@U) (i@@13 Int) (v@@29 T@U) ) (! (let ((T@@118 (type v@@29)))
 (=> (= (type s@@21) (SeqType T@@118)) (=> (and (<= 0 i@@13) (< i@@13 (|Seq#Length| s@@21))) (= (|Seq#Length| (|Seq#Update| s@@21 i@@13 v@@29)) (|Seq#Length| s@@21)))))
 :qid |DafnyPre.966:18|
 :skolemid |545|
 :pattern ( (|Seq#Length| (|Seq#Update| s@@21 i@@13 v@@29)))
)))
(assert (forall ((s@@22 T@U) (i@@14 Int) (v@@30 T@U) (n@@7 Int) ) (! (let ((T@@119 (type v@@30)))
 (=> (= (type s@@22) (SeqType T@@119)) (=> (and (<= 0 n@@7) (< n@@7 (|Seq#Length| s@@22))) (and (=> (= i@@14 n@@7) (= (|Seq#Index| (|Seq#Update| s@@22 i@@14 v@@30) n@@7) v@@30)) (=> (not (= i@@14 n@@7)) (= (|Seq#Index| (|Seq#Update| s@@22 i@@14 v@@30) n@@7) (|Seq#Index| s@@22 n@@7)))))))
 :qid |DafnyPre.968:18|
 :skolemid |546|
 :pattern ( (|Seq#Index| (|Seq#Update| s@@22 i@@14 v@@30) n@@7))
)))
(assert (forall ((s@@23 T@U) (x@@36 T@U) ) (! (let ((T@@120 (type x@@36)))
 (=> (= (type s@@23) (SeqType T@@120)) (and (=> (|Seq#Contains| s@@23 x@@36) (exists ((i@@15 Int) ) (!  (and (and (<= 0 i@@15) (< i@@15 (|Seq#Length| s@@23))) (= (|Seq#Index| s@@23 i@@15) x@@36))
 :qid |DafnyPre.976:13|
 :skolemid |547|
 :pattern ( (|Seq#Index| s@@23 i@@15))
))) (=> (exists ((i@@16 Int) ) (!  (and (and (<= 0 i@@16) (< i@@16 (|Seq#Length| s@@23))) (= (|Seq#Index| s@@23 i@@16) x@@36))
 :qid |DafnyPre.976:13|
 :skolemid |547|
 :pattern ( (|Seq#Index| s@@23 i@@16))
)) (|Seq#Contains| s@@23 x@@36)))))
 :qid |DafnyPre.974:18|
 :skolemid |548|
 :pattern ( (|Seq#Contains| s@@23 x@@36))
)))
(assert (forall ((x@@37 T@U) ) (! (let ((T@@121 (type x@@37)))
 (not (|Seq#Contains| (|Seq#Empty| T@@121) x@@37)))
 :qid |DafnyPre.977:18|
 :skolemid |549|
 :pattern ( (let ((T@@121 (type x@@37)))
(|Seq#Contains| (|Seq#Empty| T@@121) x@@37)))
)))
(assert (forall ((s0@@2 T@U) (s1@@2 T@U) (x@@38 T@U) ) (! (let ((T@@122 (type x@@38)))
 (=> (and (= (type s0@@2) (SeqType T@@122)) (= (type s1@@2) (SeqType T@@122))) (and (=> (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@38) (or (|Seq#Contains| s0@@2 x@@38) (|Seq#Contains| s1@@2 x@@38))) (=> (or (|Seq#Contains| s0@@2 x@@38) (|Seq#Contains| s1@@2 x@@38)) (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@38)))))
 :qid |DafnyPre.981:18|
 :skolemid |550|
 :pattern ( (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@38))
)))
(assert (forall ((s@@24 T@U) (v@@31 T@U) (x@@39 T@U) ) (! (let ((T@@123 (type v@@31)))
 (=> (and (= (type s@@24) (SeqType T@@123)) (= (type x@@39) T@@123)) (and (=> (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@39) (or (= v@@31 x@@39) (|Seq#Contains| s@@24 x@@39))) (=> (or (= v@@31 x@@39) (|Seq#Contains| s@@24 x@@39)) (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@39)))))
 :qid |DafnyPre.986:18|
 :skolemid |551|
 :pattern ( (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@39))
)))
(assert (forall ((arg0@@94 T@U) (arg1@@40 Int) ) (! (let ((T@@124 (SeqTypeInv0 (type arg0@@94))))
(= (type (|Seq#Take| arg0@@94 arg1@@40)) (SeqType T@@124)))
 :qid |funType:Seq#Take|
 :pattern ( (|Seq#Take| arg0@@94 arg1@@40))
)))
(assert (forall ((s@@25 T@U) (n@@8 Int) (x@@40 T@U) ) (! (let ((T@@125 (type x@@40)))
 (=> (= (type s@@25) (SeqType T@@125)) (and (=> (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@40) (exists ((i@@17 Int) ) (!  (and (and (and (<= 0 i@@17) (< i@@17 n@@8)) (< i@@17 (|Seq#Length| s@@25))) (= (|Seq#Index| s@@25 i@@17) x@@40))
 :qid |DafnyPre.993:13|
 :skolemid |552|
 :pattern ( (|Seq#Index| s@@25 i@@17))
))) (=> (exists ((i@@18 Int) ) (!  (and (and (and (<= 0 i@@18) (< i@@18 n@@8)) (< i@@18 (|Seq#Length| s@@25))) (= (|Seq#Index| s@@25 i@@18) x@@40))
 :qid |DafnyPre.993:13|
 :skolemid |552|
 :pattern ( (|Seq#Index| s@@25 i@@18))
)) (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@40)))))
 :qid |DafnyPre.990:18|
 :skolemid |553|
 :pattern ( (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@40))
)))
(assert (forall ((arg0@@95 T@U) (arg1@@41 Int) ) (! (let ((T@@126 (SeqTypeInv0 (type arg0@@95))))
(= (type (|Seq#Drop| arg0@@95 arg1@@41)) (SeqType T@@126)))
 :qid |funType:Seq#Drop|
 :pattern ( (|Seq#Drop| arg0@@95 arg1@@41))
)))
(assert (forall ((s@@26 T@U) (n@@9 Int) (x@@41 T@U) ) (! (let ((T@@127 (type x@@41)))
 (=> (= (type s@@26) (SeqType T@@127)) (and (=> (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@41) (exists ((i@@19 Int) ) (!  (and (and (and (<= 0 n@@9) (<= n@@9 i@@19)) (< i@@19 (|Seq#Length| s@@26))) (= (|Seq#Index| s@@26 i@@19) x@@41))
 :qid |DafnyPre.998:13|
 :skolemid |554|
 :pattern ( (|Seq#Index| s@@26 i@@19))
))) (=> (exists ((i@@20 Int) ) (!  (and (and (and (<= 0 n@@9) (<= n@@9 i@@20)) (< i@@20 (|Seq#Length| s@@26))) (= (|Seq#Index| s@@26 i@@20) x@@41))
 :qid |DafnyPre.998:13|
 :skolemid |554|
 :pattern ( (|Seq#Index| s@@26 i@@20))
)) (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@41)))))
 :qid |DafnyPre.995:18|
 :skolemid |555|
 :pattern ( (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@41))
)))
(assert (forall ((s0@@3 T@U) (s1@@3 T@U) ) (! (let ((T@@128 (SeqTypeInv0 (type s0@@3))))
 (=> (and (= (type s0@@3) (SeqType T@@128)) (= (type s1@@3) (SeqType T@@128))) (and (=> (|Seq#Equal| s0@@3 s1@@3) (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j Int) ) (!  (=> (and (<= 0 j) (< j (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j) (|Seq#Index| s1@@3 j)))
 :qid |DafnyPre.1005:13|
 :skolemid |556|
 :pattern ( (|Seq#Index| s0@@3 j))
 :pattern ( (|Seq#Index| s1@@3 j))
)))) (=> (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j@@0) (|Seq#Index| s1@@3 j@@0)))
 :qid |DafnyPre.1005:13|
 :skolemid |556|
 :pattern ( (|Seq#Index| s0@@3 j@@0))
 :pattern ( (|Seq#Index| s1@@3 j@@0))
))) (|Seq#Equal| s0@@3 s1@@3)))))
 :qid |DafnyPre.1002:18|
 :skolemid |557|
 :pattern ( (|Seq#Equal| s0@@3 s1@@3))
)))
(assert (forall ((a@@67 T@U) (b@@51 T@U) ) (! (let ((T@@129 (SeqTypeInv0 (type a@@67))))
 (=> (and (and (= (type a@@67) (SeqType T@@129)) (= (type b@@51) (SeqType T@@129))) (|Seq#Equal| a@@67 b@@51)) (= a@@67 b@@51)))
 :qid |DafnyPre.1007:18|
 :skolemid |558|
 :pattern ( (|Seq#Equal| a@@67 b@@51))
)))
(assert (forall ((s0@@4 T@U) (s1@@4 T@U) (n@@10 Int) ) (! (let ((T@@130 (SeqTypeInv0 (type s0@@4))))
 (=> (and (= (type s0@@4) (SeqType T@@130)) (= (type s1@@4) (SeqType T@@130))) (and (=> (|Seq#SameUntil| s0@@4 s1@@4 n@@10) (forall ((j@@1 Int) ) (!  (=> (and (<= 0 j@@1) (< j@@1 n@@10)) (= (|Seq#Index| s0@@4 j@@1) (|Seq#Index| s1@@4 j@@1)))
 :qid |DafnyPre.1013:13|
 :skolemid |559|
 :pattern ( (|Seq#Index| s0@@4 j@@1))
 :pattern ( (|Seq#Index| s1@@4 j@@1))
))) (=> (forall ((j@@2 Int) ) (!  (=> (and (<= 0 j@@2) (< j@@2 n@@10)) (= (|Seq#Index| s0@@4 j@@2) (|Seq#Index| s1@@4 j@@2)))
 :qid |DafnyPre.1013:13|
 :skolemid |559|
 :pattern ( (|Seq#Index| s0@@4 j@@2))
 :pattern ( (|Seq#Index| s1@@4 j@@2))
)) (|Seq#SameUntil| s0@@4 s1@@4 n@@10)))))
 :qid |DafnyPre.1011:18|
 :skolemid |560|
 :pattern ( (|Seq#SameUntil| s0@@4 s1@@4 n@@10))
)))
(assert (forall ((s@@27 T@U) (n@@11 Int) ) (! (let ((T@@131 (SeqTypeInv0 (type s@@27))))
 (=> (= (type s@@27) (SeqType T@@131)) (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length| s@@27))) (= (|Seq#Length| (|Seq#Take| s@@27 n@@11)) n@@11))))
 :qid |DafnyPre.1017:18|
 :skolemid |561|
 :pattern ( (|Seq#Length| (|Seq#Take| s@@27 n@@11)))
)))
(assert (forall ((s@@28 T@U) (n@@12 Int) (j@@3 Int) ) (! (let ((T@@132 (SeqTypeInv0 (type s@@28))))
 (=> (= (type s@@28) (SeqType T@@132)) (=> (and (and (<= 0 j@@3) (< j@@3 n@@12)) (< j@@3 (|Seq#Length| s@@28))) (= (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@3) (|Seq#Index| s@@28 j@@3)))))
 :qid |DafnyPre.1019:18|
 :weight 25
 :skolemid |562|
 :pattern ( (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@3))
 :pattern ( (|Seq#Index| s@@28 j@@3) (|Seq#Take| s@@28 n@@12))
)))
(assert (forall ((s@@29 T@U) (n@@13 Int) ) (! (let ((T@@133 (SeqTypeInv0 (type s@@29))))
 (=> (= (type s@@29) (SeqType T@@133)) (=> (and (<= 0 n@@13) (<= n@@13 (|Seq#Length| s@@29))) (= (|Seq#Length| (|Seq#Drop| s@@29 n@@13)) (- (|Seq#Length| s@@29) n@@13)))))
 :qid |DafnyPre.1027:18|
 :skolemid |563|
 :pattern ( (|Seq#Length| (|Seq#Drop| s@@29 n@@13)))
)))
(assert (forall ((s@@30 T@U) (n@@14 Int) (j@@4 Int) ) (! (let ((T@@134 (SeqTypeInv0 (type s@@30))))
 (=> (= (type s@@30) (SeqType T@@134)) (=> (and (and (<= 0 n@@14) (<= 0 j@@4)) (< j@@4 (- (|Seq#Length| s@@30) n@@14))) (= (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@4) (|Seq#Index| s@@30 (+ j@@4 n@@14))))))
 :qid |DafnyPre.1029:18|
 :weight 25
 :skolemid |564|
 :pattern ( (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@4))
)))
(assert (forall ((s@@31 T@U) (n@@15 Int) (k@@3 Int) ) (! (let ((T@@135 (SeqTypeInv0 (type s@@31))))
 (=> (= (type s@@31) (SeqType T@@135)) (=> (and (and (<= 0 n@@15) (<= n@@15 k@@3)) (< k@@3 (|Seq#Length| s@@31))) (= (|Seq#Index| (|Seq#Drop| s@@31 n@@15) (- k@@3 n@@15)) (|Seq#Index| s@@31 k@@3)))))
 :qid |DafnyPre.1034:18|
 :weight 25
 :skolemid |565|
 :pattern ( (|Seq#Index| s@@31 k@@3) (|Seq#Drop| s@@31 n@@15))
)))
(assert (forall ((s@@32 T@U) (t@@28 T@U) (n@@16 Int) ) (! (let ((T@@136 (SeqTypeInv0 (type s@@32))))
 (=> (and (and (= (type s@@32) (SeqType T@@136)) (= (type t@@28) (SeqType T@@136))) (= n@@16 (|Seq#Length| s@@32))) (and (= (|Seq#Take| (|Seq#Append| s@@32 t@@28) n@@16) s@@32) (= (|Seq#Drop| (|Seq#Append| s@@32 t@@28) n@@16) t@@28))))
 :qid |DafnyPre.1040:18|
 :skolemid |566|
 :pattern ( (|Seq#Take| (|Seq#Append| s@@32 t@@28) n@@16))
 :pattern ( (|Seq#Drop| (|Seq#Append| s@@32 t@@28) n@@16))
)))
(assert (forall ((arg0@@96 T@U) (arg1@@42 T@U) ) (! (= (type (|Seq#FromArray| arg0@@96 arg1@@42)) (SeqType BoxType))
 :qid |funType:Seq#FromArray|
 :pattern ( (|Seq#FromArray| arg0@@96 arg1@@42))
)))
(assert (forall ((h@@16 T@U) (a@@68 T@U) ) (!  (=> (and (= (type h@@16) (MapType0Type refType MapType1Type)) (= (type a@@68) refType)) (= (|Seq#Length| (|Seq#FromArray| h@@16 a@@68)) (_System.array.Length a@@68)))
 :qid |DafnyPre.1049:15|
 :skolemid |567|
 :pattern ( (|Seq#Length| (|Seq#FromArray| h@@16 a@@68)))
)))
(assert (forall ((h@@17 T@U) (a@@69 T@U) ) (!  (=> (and (= (type h@@17) (MapType0Type refType MapType1Type)) (= (type a@@69) refType)) (forall ((i@@21 Int) ) (!  (=> (and (<= 0 i@@21) (< i@@21 (|Seq#Length| (|Seq#FromArray| h@@17 a@@69)))) (= (|Seq#Index| (|Seq#FromArray| h@@17 a@@69) i@@21) (MapType1Select (MapType0Select h@@17 a@@69) (IndexField i@@21))))
 :qid |DafnyPre.1054:11|
 :skolemid |568|
 :pattern ( (MapType1Select (MapType0Select h@@17 a@@69) (IndexField i@@21)))
 :pattern ( (|Seq#Index| (|Seq#FromArray| h@@17 a@@69) i@@21))
)))
 :qid |DafnyPre.1052:15|
 :skolemid |569|
 :pattern ( (|Seq#FromArray| h@@17 a@@69))
)))
(assert (forall ((h0 T@U) (h1 T@U) (a@@70 T@U) ) (!  (=> (and (and (= (type h0) (MapType0Type refType MapType1Type)) (= (type h1) (MapType0Type refType MapType1Type))) (= (type a@@70) refType)) (=> (and (and (and ($IsGoodHeap h0) ($IsGoodHeap h1)) ($HeapSucc h0 h1)) (= (MapType0Select h0 a@@70) (MapType0Select h1 a@@70))) (= (|Seq#FromArray| h0 a@@70) (|Seq#FromArray| h1 a@@70))))
 :qid |DafnyPre.1064:15|
 :skolemid |570|
 :pattern ( (|Seq#FromArray| h1 a@@70) ($HeapSucc h0 h1))
)))
(assert (forall ((h@@18 T@U) (i@@22 Int) (v@@32 T@U) (a@@71 T@U) ) (!  (=> (and (and (and (= (type h@@18) (MapType0Type refType MapType1Type)) (= (type v@@32) BoxType)) (= (type a@@71) refType)) (and (<= 0 i@@22) (< i@@22 (_System.array.Length a@@71)))) (= (|Seq#FromArray| (MapType0Store h@@18 a@@71 (MapType1Store (MapType0Select h@@18 a@@71) (IndexField i@@22) v@@32)) a@@71) (|Seq#Update| (|Seq#FromArray| h@@18 a@@71) i@@22 v@@32)))
 :qid |DafnyPre.1069:15|
 :skolemid |571|
 :pattern ( (|Seq#FromArray| (MapType0Store h@@18 a@@71 (MapType1Store (MapType0Select h@@18 a@@71) (IndexField i@@22) v@@32)) a@@71))
)))
(assert (forall ((s@@33 T@U) (i@@23 Int) (v@@33 T@U) (n@@17 Int) ) (! (let ((T@@137 (type v@@33)))
 (=> (= (type s@@33) (SeqType T@@137)) (=> (and (and (<= 0 i@@23) (< i@@23 n@@17)) (<= n@@17 (|Seq#Length| s@@33))) (= (|Seq#Take| (|Seq#Update| s@@33 i@@23 v@@33) n@@17) (|Seq#Update| (|Seq#Take| s@@33 n@@17) i@@23 v@@33)))))
 :qid |DafnyPre.1074:18|
 :skolemid |572|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@33 i@@23 v@@33) n@@17))
)))
(assert (forall ((s@@34 T@U) (i@@24 Int) (v@@34 T@U) (n@@18 Int) ) (! (let ((T@@138 (type v@@34)))
 (=> (= (type s@@34) (SeqType T@@138)) (=> (and (<= n@@18 i@@24) (< i@@24 (|Seq#Length| s@@34))) (= (|Seq#Take| (|Seq#Update| s@@34 i@@24 v@@34) n@@18) (|Seq#Take| s@@34 n@@18)))))
 :qid |DafnyPre.1077:18|
 :skolemid |573|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@34 i@@24 v@@34) n@@18))
)))
(assert (forall ((s@@35 T@U) (i@@25 Int) (v@@35 T@U) (n@@19 Int) ) (! (let ((T@@139 (type v@@35)))
 (=> (= (type s@@35) (SeqType T@@139)) (=> (and (and (<= 0 n@@19) (<= n@@19 i@@25)) (< i@@25 (|Seq#Length| s@@35))) (= (|Seq#Drop| (|Seq#Update| s@@35 i@@25 v@@35) n@@19) (|Seq#Update| (|Seq#Drop| s@@35 n@@19) (- i@@25 n@@19) v@@35)))))
 :qid |DafnyPre.1080:18|
 :skolemid |574|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@35 i@@25 v@@35) n@@19))
)))
(assert (forall ((s@@36 T@U) (i@@26 Int) (v@@36 T@U) (n@@20 Int) ) (! (let ((T@@140 (type v@@36)))
 (=> (= (type s@@36) (SeqType T@@140)) (=> (and (and (<= 0 i@@26) (< i@@26 n@@20)) (< n@@20 (|Seq#Length| s@@36))) (= (|Seq#Drop| (|Seq#Update| s@@36 i@@26 v@@36) n@@20) (|Seq#Drop| s@@36 n@@20)))))
 :qid |DafnyPre.1083:18|
 :skolemid |575|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@36 i@@26 v@@36) n@@20))
)))
(assert (forall ((h@@19 T@U) (a@@72 T@U) (n0 Int) (n1 Int) ) (!  (=> (and (= (type h@@19) (MapType0Type refType MapType1Type)) (= (type a@@72) refType)) (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@72))) (= (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n1) (|Seq#Build| (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n0) (MapType1Select (MapType0Select h@@19 a@@72) (IndexField n0))))))
 :qid |DafnyPre.1087:15|
 :skolemid |576|
 :pattern ( (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n0) (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n1))
)))
(assert (forall ((s@@37 T@U) (v@@37 T@U) (n@@21 Int) ) (! (let ((T@@141 (type v@@37)))
 (=> (= (type s@@37) (SeqType T@@141)) (=> (and (<= 0 n@@21) (<= n@@21 (|Seq#Length| s@@37))) (= (|Seq#Drop| (|Seq#Build| s@@37 v@@37) n@@21) (|Seq#Build| (|Seq#Drop| s@@37 n@@21) v@@37)))))
 :qid |DafnyPre.1091:18|
 :skolemid |577|
 :pattern ( (|Seq#Drop| (|Seq#Build| s@@37 v@@37) n@@21))
)))
(assert (forall ((s@@38 T@U) (i@@27 Int) ) (!  (=> (= (type s@@38) (SeqType BoxType)) (=> (and (<= 0 i@@27) (< i@@27 (|Seq#Length| s@@38))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@27))) (|Seq#Rank| s@@38))))
 :qid |DafnyPre.1096:15|
 :skolemid |578|
 :pattern ( (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@27))))
)))
(assert (forall ((s@@39 T@U) (i@@28 Int) ) (! (let ((T@@142 (SeqTypeInv0 (type s@@39))))
 (=> (= (type s@@39) (SeqType T@@142)) (=> (and (< 0 i@@28) (<= i@@28 (|Seq#Length| s@@39))) (< (|Seq#Rank| (|Seq#Drop| s@@39 i@@28)) (|Seq#Rank| s@@39)))))
 :qid |DafnyPre.1099:18|
 :skolemid |579|
 :pattern ( (|Seq#Rank| (|Seq#Drop| s@@39 i@@28)))
)))
(assert (forall ((s@@40 T@U) (i@@29 Int) ) (! (let ((T@@143 (SeqTypeInv0 (type s@@40))))
 (=> (= (type s@@40) (SeqType T@@143)) (=> (and (<= 0 i@@29) (< i@@29 (|Seq#Length| s@@40))) (< (|Seq#Rank| (|Seq#Take| s@@40 i@@29)) (|Seq#Rank| s@@40)))))
 :qid |DafnyPre.1102:18|
 :skolemid |580|
 :pattern ( (|Seq#Rank| (|Seq#Take| s@@40 i@@29)))
)))
(assert (forall ((s@@41 T@U) (i@@30 Int) (j@@5 Int) ) (! (let ((T@@144 (SeqTypeInv0 (type s@@41))))
 (=> (= (type s@@41) (SeqType T@@144)) (=> (and (and (<= 0 i@@30) (< i@@30 j@@5)) (<= j@@5 (|Seq#Length| s@@41))) (< (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@30) (|Seq#Drop| s@@41 j@@5))) (|Seq#Rank| s@@41)))))
 :qid |DafnyPre.1105:18|
 :skolemid |581|
 :pattern ( (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@30) (|Seq#Drop| s@@41 j@@5))))
)))
(assert (forall ((s@@42 T@U) (n@@22 Int) ) (! (let ((T@@145 (SeqTypeInv0 (type s@@42))))
 (=> (and (= (type s@@42) (SeqType T@@145)) (= n@@22 0)) (= (|Seq#Drop| s@@42 n@@22) s@@42)))
 :qid |DafnyPre.1110:18|
 :skolemid |582|
 :pattern ( (|Seq#Drop| s@@42 n@@22))
)))
(assert (forall ((s@@43 T@U) (n@@23 Int) ) (! (let ((T@@146 (SeqTypeInv0 (type s@@43))))
 (=> (and (= (type s@@43) (SeqType T@@146)) (= n@@23 0)) (= (|Seq#Take| s@@43 n@@23) (|Seq#Empty| T@@146))))
 :qid |DafnyPre.1112:18|
 :skolemid |583|
 :pattern ( (|Seq#Take| s@@43 n@@23))
)))
(assert (forall ((s@@44 T@U) (m@@9 Int) (n@@24 Int) ) (! (let ((T@@147 (SeqTypeInv0 (type s@@44))))
 (=> (= (type s@@44) (SeqType T@@147)) (=> (and (and (<= 0 m@@9) (<= 0 n@@24)) (<= (+ m@@9 n@@24) (|Seq#Length| s@@44))) (= (|Seq#Drop| (|Seq#Drop| s@@44 m@@9) n@@24) (|Seq#Drop| s@@44 (+ m@@9 n@@24))))))
 :qid |DafnyPre.1114:18|
 :skolemid |584|
 :pattern ( (|Seq#Drop| (|Seq#Drop| s@@44 m@@9) n@@24))
)))
(assert (forall ((m@@10 T@U) ) (! (let ((V@@1 (MapTypeInv1 (type m@@10))))
(let ((U@@3 (MapTypeInv0 (type m@@10))))
 (=> (= (type m@@10) (MapType U@@3 V@@1)) (<= 0 (|Map#Card| m@@10)))))
 :qid |DafnyPre.1132:20|
 :skolemid |585|
 :pattern ( (|Map#Card| m@@10))
)))
(assert (forall ((m@@11 T@U) ) (! (let ((V@@2 (MapTypeInv1 (type m@@11))))
(let ((U@@4 (MapTypeInv0 (type m@@11))))
 (=> (= (type m@@11) (MapType U@@4 V@@2)) (= (|Set#Card| (|Map#Domain| m@@11)) (|Map#Card| m@@11)))))
 :qid |DafnyPre.1137:20|
 :skolemid |586|
 :pattern ( (|Set#Card| (|Map#Domain| m@@11)))
)))
(assert (forall ((arg0@@97 T@U) ) (! (let ((V@@3 (MapTypeInv1 (type arg0@@97))))
(= (type (|Map#Values| arg0@@97)) (MapType0Type V@@3 boolType)))
 :qid |funType:Map#Values|
 :pattern ( (|Map#Values| arg0@@97))
)))
(assert (forall ((m@@12 T@U) (v@@38 T@U) ) (! (let ((V@@4 (type v@@38)))
(let ((U@@5 (MapTypeInv0 (type m@@12))))
 (=> (= (type m@@12) (MapType U@@5 V@@4)) (and (=> (U_2_bool (MapType0Select (|Map#Values| m@@12) v@@38)) (exists ((u@@5 T@U) ) (!  (and (= (type u@@5) U@@5) (and (U_2_bool (MapType0Select (|Map#Domain| m@@12) u@@5)) (= v@@38 (MapType0Select (|Map#Elements| m@@12) u@@5))))
 :qid |DafnyPre.1149:10|
 :skolemid |587|
 :pattern ( (MapType0Select (|Map#Domain| m@@12) u@@5))
 :pattern ( (MapType0Select (|Map#Elements| m@@12) u@@5))
))) (=> (exists ((u@@6 T@U) ) (!  (and (= (type u@@6) U@@5) (and (U_2_bool (MapType0Select (|Map#Domain| m@@12) u@@6)) (= v@@38 (MapType0Select (|Map#Elements| m@@12) u@@6))))
 :qid |DafnyPre.1149:10|
 :skolemid |587|
 :pattern ( (MapType0Select (|Map#Domain| m@@12) u@@6))
 :pattern ( (MapType0Select (|Map#Elements| m@@12) u@@6))
)) (U_2_bool (MapType0Select (|Map#Values| m@@12) v@@38)))))))
 :qid |DafnyPre.1147:20|
 :skolemid |588|
 :pattern ( (MapType0Select (|Map#Values| m@@12) v@@38))
)))
(assert (forall ((arg0@@98 T@U) ) (! (= (type (|Map#Items| arg0@@98)) (MapType0Type BoxType boolType))
 :qid |funType:Map#Items|
 :pattern ( (|Map#Items| arg0@@98))
)))
(assert (forall ((m@@13 T@U) ) (! (let ((V@@5 (MapTypeInv1 (type m@@13))))
(let ((U@@6 (MapTypeInv0 (type m@@13))))
 (=> (= (type m@@13) (MapType U@@6 V@@5)) (= (|Set#Card| (|Map#Items| m@@13)) (|Map#Card| m@@13)))))
 :qid |DafnyPre.1168:20|
 :skolemid |589|
 :pattern ( (|Set#Card| (|Map#Items| m@@13)))
)))
(assert  (and (forall ((arg0@@99 T@U) ) (! (= (type (_System.Tuple2._0 arg0@@99)) BoxType)
 :qid |funType:_System.Tuple2._0|
 :pattern ( (_System.Tuple2._0 arg0@@99))
)) (forall ((arg0@@100 T@U) ) (! (= (type (_System.Tuple2._1 arg0@@100)) BoxType)
 :qid |funType:_System.Tuple2._1|
 :pattern ( (_System.Tuple2._1 arg0@@100))
))))
(assert (forall ((m@@14 T@U) (item T@U) ) (!  (=> (and (= (type m@@14) (MapType BoxType BoxType)) (= (type item) BoxType)) (and (=> (U_2_bool (MapType0Select (|Map#Items| m@@14) item)) (and (U_2_bool (MapType0Select (|Map#Domain| m@@14) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select (|Map#Elements| m@@14) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item))))) (=> (and (U_2_bool (MapType0Select (|Map#Domain| m@@14) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select (|Map#Elements| m@@14) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item)))) (U_2_bool (MapType0Select (|Map#Items| m@@14) item)))))
 :qid |DafnyPre.1171:15|
 :skolemid |590|
 :pattern ( (MapType0Select (|Map#Items| m@@14) item))
)))
(assert (forall ((U@@7 T@T) (V@@6 T@T) ) (! (= (type (|Map#Empty| U@@7 V@@6)) (MapType U@@7 V@@6))
 :qid |funType:Map#Empty|
 :pattern ( (|Map#Empty| U@@7 V@@6))
)))
(assert (forall ((u@@7 T@U) (V@@7 T@T) ) (! (let ((U@@8 (type u@@7)))
 (not (U_2_bool (MapType0Select (|Map#Domain| (|Map#Empty| U@@8 V@@7)) u@@7))))
 :qid |DafnyPre.1179:21|
 :skolemid |591|
 :pattern ( (let ((U@@8 (type u@@7)))
(MapType0Select (|Map#Domain| (|Map#Empty| U@@8 V@@7)) u@@7)))
)))
(assert (forall ((m@@15 T@U) ) (! (let ((V@@8 (MapTypeInv1 (type m@@15))))
(let ((U@@9 (MapTypeInv0 (type m@@15))))
 (=> (= (type m@@15) (MapType U@@9 V@@8)) (and (and (=> (= (|Map#Card| m@@15) 0) (= m@@15 (|Map#Empty| U@@9 V@@8))) (=> (= m@@15 (|Map#Empty| U@@9 V@@8)) (= (|Map#Card| m@@15) 0))) (=> (not (= (|Map#Card| m@@15) 0)) (exists ((x@@42 T@U) ) (!  (and (= (type x@@42) U@@9) (U_2_bool (MapType0Select (|Map#Domain| m@@15) x@@42)))
 :qid |DafnyPre.1184:32|
 :skolemid |592|
 :no-pattern (type x@@42)
 :no-pattern (U_2_int x@@42)
 :no-pattern (U_2_bool x@@42)
)))))))
 :qid |DafnyPre.1182:21|
 :skolemid |593|
 :pattern ( (|Map#Card| m@@15))
)))
(assert (forall ((arg0@@101 T@U) (arg1@@43 T@U) (arg2@@4 T@U) ) (! (let ((V@@9 (MapType0TypeInv1 (type arg1@@43))))
(let ((U@@10 (MapType0TypeInv0 (type arg0@@101))))
(= (type (|Map#Glue| arg0@@101 arg1@@43 arg2@@4)) (MapType U@@10 V@@9))))
 :qid |funType:Map#Glue|
 :pattern ( (|Map#Glue| arg0@@101 arg1@@43 arg2@@4))
)))
(assert (forall ((a@@73 T@U) (b@@52 T@U) (t@@29 T@U) ) (! (let ((V@@10 (MapType0TypeInv1 (type b@@52))))
(let ((U@@11 (MapType0TypeInv0 (type a@@73))))
 (=> (and (and (= (type a@@73) (MapType0Type U@@11 boolType)) (= (type b@@52) (MapType0Type U@@11 V@@10))) (= (type t@@29) TyType)) (= (|Map#Domain| (|Map#Glue| a@@73 b@@52 t@@29)) a@@73))))
 :qid |DafnyPre.1187:21|
 :skolemid |594|
 :pattern ( (|Map#Domain| (|Map#Glue| a@@73 b@@52 t@@29)))
)))
(assert (forall ((a@@74 T@U) (b@@53 T@U) (t@@30 T@U) ) (! (let ((V@@11 (MapType0TypeInv1 (type b@@53))))
(let ((U@@12 (MapType0TypeInv0 (type a@@74))))
 (=> (and (and (= (type a@@74) (MapType0Type U@@12 boolType)) (= (type b@@53) (MapType0Type U@@12 V@@11))) (= (type t@@30) TyType)) (= (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@30)) b@@53))))
 :qid |DafnyPre.1190:21|
 :skolemid |595|
 :pattern ( (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@30)))
)))
(assert (forall ((a@@75 T@U) (b@@54 T@U) (t@@31 T@U) ) (! (let ((V@@12 (MapType0TypeInv1 (type b@@54))))
(let ((U@@13 (MapType0TypeInv0 (type a@@75))))
 (=> (and (and (= (type a@@75) (MapType0Type U@@13 boolType)) (= (type b@@54) (MapType0Type U@@13 V@@12))) (= (type t@@31) TyType)) ($Is (|Map#Glue| a@@75 b@@54 t@@31) t@@31))))
 :qid |DafnyPre.1193:21|
 :skolemid |596|
 :pattern ( ($Is (|Map#Glue| a@@75 b@@54 t@@31) t@@31))
)))
(assert (forall ((arg0@@102 T@U) (arg1@@44 T@U) (arg2@@5 T@U) ) (! (let ((V@@13 (type arg2@@5)))
(let ((U@@14 (type arg1@@44)))
(= (type (|Map#Build| arg0@@102 arg1@@44 arg2@@5)) (MapType U@@14 V@@13))))
 :qid |funType:Map#Build|
 :pattern ( (|Map#Build| arg0@@102 arg1@@44 arg2@@5))
)))
(assert (forall ((m@@16 T@U) (u@@8 T@U) (|u'| T@U) (v@@39 T@U) ) (! (let ((V@@14 (type v@@39)))
(let ((U@@15 (type u@@8)))
 (=> (and (= (type m@@16) (MapType U@@15 V@@14)) (= (type |u'|) U@@15)) (and (=> (= |u'| u@@8) (and (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@16 u@@8 v@@39)) |u'|)) (= (MapType0Select (|Map#Elements| (|Map#Build| m@@16 u@@8 v@@39)) |u'|) v@@39))) (=> (not (= |u'| u@@8)) (and (and (=> (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@16 u@@8 v@@39)) |u'|)) (U_2_bool (MapType0Select (|Map#Domain| m@@16) |u'|))) (=> (U_2_bool (MapType0Select (|Map#Domain| m@@16) |u'|)) (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@16 u@@8 v@@39)) |u'|)))) (= (MapType0Select (|Map#Elements| (|Map#Build| m@@16 u@@8 v@@39)) |u'|) (MapType0Select (|Map#Elements| m@@16) |u'|))))))))
 :qid |DafnyPre.1204:21|
 :skolemid |597|
 :pattern ( (MapType0Select (|Map#Domain| (|Map#Build| m@@16 u@@8 v@@39)) |u'|))
 :pattern ( (MapType0Select (|Map#Elements| (|Map#Build| m@@16 u@@8 v@@39)) |u'|))
)))
(assert (forall ((m@@17 T@U) (u@@9 T@U) (v@@40 T@U) ) (! (let ((V@@15 (type v@@40)))
(let ((U@@16 (type u@@9)))
 (=> (and (= (type m@@17) (MapType U@@16 V@@15)) (U_2_bool (MapType0Select (|Map#Domain| m@@17) u@@9))) (= (|Map#Card| (|Map#Build| m@@17 u@@9 v@@40)) (|Map#Card| m@@17)))))
 :qid |DafnyPre.1210:21|
 :skolemid |598|
 :pattern ( (|Map#Card| (|Map#Build| m@@17 u@@9 v@@40)))
)))
(assert (forall ((m@@18 T@U) (u@@10 T@U) (v@@41 T@U) ) (! (let ((V@@16 (type v@@41)))
(let ((U@@17 (type u@@10)))
 (=> (and (= (type m@@18) (MapType U@@17 V@@16)) (not (U_2_bool (MapType0Select (|Map#Domain| m@@18) u@@10)))) (= (|Map#Card| (|Map#Build| m@@18 u@@10 v@@41)) (+ (|Map#Card| m@@18) 1)))))
 :qid |DafnyPre.1212:21|
 :skolemid |599|
 :pattern ( (|Map#Card| (|Map#Build| m@@18 u@@10 v@@41)))
)))
(assert (forall ((m@@19 T@U) (|m'| T@U) ) (! (let ((V@@17 (MapTypeInv1 (type m@@19))))
(let ((U@@18 (MapTypeInv0 (type m@@19))))
 (=> (and (= (type m@@19) (MapType U@@18 V@@17)) (= (type |m'|) (MapType U@@18 V@@17))) (and (=> (|Map#Equal| m@@19 |m'|) (and (forall ((u@@11 T@U) ) (!  (=> (= (type u@@11) U@@18) (and (=> (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@11)) (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@11))) (=> (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@11)) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@11)))))
 :qid |DafnyPre.1219:35|
 :skolemid |600|
 :no-pattern (type u@@11)
 :no-pattern (U_2_int u@@11)
 :no-pattern (U_2_bool u@@11)
)) (forall ((u@@12 T@U) ) (!  (=> (and (= (type u@@12) U@@18) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@12))) (= (MapType0Select (|Map#Elements| m@@19) u@@12) (MapType0Select (|Map#Elements| |m'|) u@@12)))
 :qid |DafnyPre.1220:35|
 :skolemid |601|
 :no-pattern (type u@@12)
 :no-pattern (U_2_int u@@12)
 :no-pattern (U_2_bool u@@12)
)))) (=> (and (forall ((u@@13 T@U) ) (!  (=> (= (type u@@13) U@@18) (and (=> (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@13)) (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@13))) (=> (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@13)) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@13)))))
 :qid |DafnyPre.1219:35|
 :skolemid |600|
 :no-pattern (type u@@13)
 :no-pattern (U_2_int u@@13)
 :no-pattern (U_2_bool u@@13)
)) (forall ((u@@14 T@U) ) (!  (=> (and (= (type u@@14) U@@18) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@14))) (= (MapType0Select (|Map#Elements| m@@19) u@@14) (MapType0Select (|Map#Elements| |m'|) u@@14)))
 :qid |DafnyPre.1220:35|
 :skolemid |601|
 :no-pattern (type u@@14)
 :no-pattern (U_2_int u@@14)
 :no-pattern (U_2_bool u@@14)
))) (|Map#Equal| m@@19 |m'|))))))
 :qid |DafnyPre.1217:21|
 :skolemid |602|
 :pattern ( (|Map#Equal| m@@19 |m'|))
)))
(assert (forall ((m@@20 T@U) (|m'@@0| T@U) ) (! (let ((V@@18 (MapTypeInv1 (type m@@20))))
(let ((U@@19 (MapTypeInv0 (type m@@20))))
 (=> (and (and (= (type m@@20) (MapType U@@19 V@@18)) (= (type |m'@@0|) (MapType U@@19 V@@18))) (|Map#Equal| m@@20 |m'@@0|)) (= m@@20 |m'@@0|))))
 :qid |DafnyPre.1222:21|
 :skolemid |603|
 :pattern ( (|Map#Equal| m@@20 |m'@@0|))
)))
(assert (forall ((m@@21 T@U) (|m'@@1| T@U) ) (! (let ((V@@19 (MapTypeInv1 (type m@@21))))
(let ((U@@20 (MapTypeInv0 (type m@@21))))
 (=> (and (= (type m@@21) (MapType U@@20 V@@19)) (= (type |m'@@1|) (MapType U@@20 V@@19))) (and (=> (|Map#Disjoint| m@@21 |m'@@1|) (forall ((o@@52 T@U) ) (!  (=> (= (type o@@52) U@@20) (or (not (U_2_bool (MapType0Select (|Map#Domain| m@@21) o@@52))) (not (U_2_bool (MapType0Select (|Map#Domain| |m'@@1|) o@@52)))))
 :qid |DafnyPre.1229:38|
 :skolemid |604|
 :pattern ( (MapType0Select (|Map#Domain| m@@21) o@@52))
 :pattern ( (MapType0Select (|Map#Domain| |m'@@1|) o@@52))
))) (=> (forall ((o@@53 T@U) ) (!  (=> (= (type o@@53) U@@20) (or (not (U_2_bool (MapType0Select (|Map#Domain| m@@21) o@@53))) (not (U_2_bool (MapType0Select (|Map#Domain| |m'@@1|) o@@53)))))
 :qid |DafnyPre.1229:38|
 :skolemid |604|
 :pattern ( (MapType0Select (|Map#Domain| m@@21) o@@53))
 :pattern ( (MapType0Select (|Map#Domain| |m'@@1|) o@@53))
)) (|Map#Disjoint| m@@21 |m'@@1|))))))
 :qid |DafnyPre.1227:21|
 :skolemid |605|
 :pattern ( (|Map#Disjoint| m@@21 |m'@@1|))
)))
(assert (forall ((arg0@@103 T@U) ) (! (let ((V@@20 (IMapTypeInv1 (type arg0@@103))))
(= (type (|IMap#Values| arg0@@103)) (MapType0Type V@@20 boolType)))
 :qid |funType:IMap#Values|
 :pattern ( (|IMap#Values| arg0@@103))
)))
(assert (forall ((m@@22 T@U) (v@@42 T@U) ) (! (let ((V@@21 (type v@@42)))
(let ((U@@21 (IMapTypeInv0 (type m@@22))))
 (=> (= (type m@@22) (IMapType U@@21 V@@21)) (and (=> (U_2_bool (MapType0Select (|IMap#Values| m@@22) v@@42)) (exists ((u@@15 T@U) ) (!  (and (= (type u@@15) U@@21) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@22) u@@15)) (= v@@42 (MapType0Select (|IMap#Elements| m@@22) u@@15))))
 :qid |DafnyPre.1252:10|
 :skolemid |606|
 :pattern ( (MapType0Select (|IMap#Domain| m@@22) u@@15))
 :pattern ( (MapType0Select (|IMap#Elements| m@@22) u@@15))
))) (=> (exists ((u@@16 T@U) ) (!  (and (= (type u@@16) U@@21) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@22) u@@16)) (= v@@42 (MapType0Select (|IMap#Elements| m@@22) u@@16))))
 :qid |DafnyPre.1252:10|
 :skolemid |606|
 :pattern ( (MapType0Select (|IMap#Domain| m@@22) u@@16))
 :pattern ( (MapType0Select (|IMap#Elements| m@@22) u@@16))
)) (U_2_bool (MapType0Select (|IMap#Values| m@@22) v@@42)))))))
 :qid |DafnyPre.1250:20|
 :skolemid |607|
 :pattern ( (MapType0Select (|IMap#Values| m@@22) v@@42))
)))
(assert (forall ((arg0@@104 T@U) ) (! (= (type (|IMap#Items| arg0@@104)) (MapType0Type BoxType boolType))
 :qid |funType:IMap#Items|
 :pattern ( (|IMap#Items| arg0@@104))
)))
(assert (forall ((m@@23 T@U) (item@@0 T@U) ) (!  (=> (and (= (type m@@23) (IMapType BoxType BoxType)) (= (type item@@0) BoxType)) (and (=> (U_2_bool (MapType0Select (|IMap#Items| m@@23) item@@0)) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select (|IMap#Elements| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0))))) (=> (and (U_2_bool (MapType0Select (|IMap#Domain| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select (|IMap#Elements| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0)))) (U_2_bool (MapType0Select (|IMap#Items| m@@23) item@@0)))))
 :qid |DafnyPre.1267:15|
 :skolemid |608|
 :pattern ( (MapType0Select (|IMap#Items| m@@23) item@@0))
)))
(assert (forall ((U@@22 T@T) (V@@22 T@T) ) (! (= (type (|IMap#Empty| U@@22 V@@22)) (IMapType U@@22 V@@22))
 :qid |funType:IMap#Empty|
 :pattern ( (|IMap#Empty| U@@22 V@@22))
)))
(assert (forall ((u@@17 T@U) (V@@23 T@T) ) (! (let ((U@@23 (type u@@17)))
 (not (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Empty| U@@23 V@@23)) u@@17))))
 :qid |DafnyPre.1274:21|
 :skolemid |609|
 :pattern ( (let ((U@@23 (type u@@17)))
(MapType0Select (|IMap#Domain| (|IMap#Empty| U@@23 V@@23)) u@@17)))
)))
(assert (forall ((arg0@@105 T@U) (arg1@@45 T@U) (arg2@@6 T@U) ) (! (let ((V@@24 (MapType0TypeInv1 (type arg1@@45))))
(let ((U@@24 (MapType0TypeInv0 (type arg0@@105))))
(= (type (|IMap#Glue| arg0@@105 arg1@@45 arg2@@6)) (IMapType U@@24 V@@24))))
 :qid |funType:IMap#Glue|
 :pattern ( (|IMap#Glue| arg0@@105 arg1@@45 arg2@@6))
)))
(assert (forall ((a@@76 T@U) (b@@55 T@U) (t@@32 T@U) ) (! (let ((V@@25 (MapType0TypeInv1 (type b@@55))))
(let ((U@@25 (MapType0TypeInv0 (type a@@76))))
 (=> (and (and (= (type a@@76) (MapType0Type U@@25 boolType)) (= (type b@@55) (MapType0Type U@@25 V@@25))) (= (type t@@32) TyType)) (= (|IMap#Domain| (|IMap#Glue| a@@76 b@@55 t@@32)) a@@76))))
 :qid |DafnyPre.1279:21|
 :skolemid |610|
 :pattern ( (|IMap#Domain| (|IMap#Glue| a@@76 b@@55 t@@32)))
)))
(assert (forall ((a@@77 T@U) (b@@56 T@U) (t@@33 T@U) ) (! (let ((V@@26 (MapType0TypeInv1 (type b@@56))))
(let ((U@@26 (MapType0TypeInv0 (type a@@77))))
 (=> (and (and (= (type a@@77) (MapType0Type U@@26 boolType)) (= (type b@@56) (MapType0Type U@@26 V@@26))) (= (type t@@33) TyType)) (= (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@33)) b@@56))))
 :qid |DafnyPre.1282:21|
 :skolemid |611|
 :pattern ( (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@33)))
)))
(assert (forall ((a@@78 T@U) (b@@57 T@U) (t@@34 T@U) ) (! (let ((V@@27 (MapType0TypeInv1 (type b@@57))))
(let ((U@@27 (MapType0TypeInv0 (type a@@78))))
 (=> (and (and (= (type a@@78) (MapType0Type U@@27 boolType)) (= (type b@@57) (MapType0Type U@@27 V@@27))) (= (type t@@34) TyType)) ($Is (|IMap#Glue| a@@78 b@@57 t@@34) t@@34))))
 :qid |DafnyPre.1285:21|
 :skolemid |612|
 :pattern ( ($Is (|IMap#Glue| a@@78 b@@57 t@@34) t@@34))
)))
(assert (forall ((arg0@@106 T@U) (arg1@@46 T@U) (arg2@@7 T@U) ) (! (let ((V@@28 (type arg2@@7)))
(let ((U@@28 (type arg1@@46)))
(= (type (|IMap#Build| arg0@@106 arg1@@46 arg2@@7)) (IMapType U@@28 V@@28))))
 :qid |funType:IMap#Build|
 :pattern ( (|IMap#Build| arg0@@106 arg1@@46 arg2@@7))
)))
(assert (forall ((m@@24 T@U) (u@@18 T@U) (|u'@@0| T@U) (v@@43 T@U) ) (! (let ((V@@29 (type v@@43)))
(let ((U@@29 (type u@@18)))
 (=> (and (= (type m@@24) (IMapType U@@29 V@@29)) (= (type |u'@@0|) U@@29)) (and (=> (= |u'@@0| u@@18) (and (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|)) (= (MapType0Select (|IMap#Elements| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|) v@@43))) (=> (not (= |u'@@0| u@@18)) (and (and (=> (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|)) (U_2_bool (MapType0Select (|IMap#Domain| m@@24) |u'@@0|))) (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@24) |u'@@0|)) (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|)))) (= (MapType0Select (|IMap#Elements| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|) (MapType0Select (|IMap#Elements| m@@24) |u'@@0|))))))))
 :qid |DafnyPre.1295:21|
 :skolemid |613|
 :pattern ( (MapType0Select (|IMap#Domain| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|))
 :pattern ( (MapType0Select (|IMap#Elements| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|))
)))
(assert (forall ((m@@25 T@U) (|m'@@2| T@U) ) (! (let ((V@@30 (IMapTypeInv1 (type m@@25))))
(let ((U@@30 (IMapTypeInv0 (type m@@25))))
 (=> (and (= (type m@@25) (IMapType U@@30 V@@30)) (= (type |m'@@2|) (IMapType U@@30 V@@30))) (and (=> (|IMap#Equal| m@@25 |m'@@2|) (and (forall ((u@@19 T@U) ) (!  (=> (= (type u@@19) U@@30) (and (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@19)) (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@19))) (=> (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@19)) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@19)))))
 :qid |DafnyPre.1306:36|
 :skolemid |614|
 :no-pattern (type u@@19)
 :no-pattern (U_2_int u@@19)
 :no-pattern (U_2_bool u@@19)
)) (forall ((u@@20 T@U) ) (!  (=> (and (= (type u@@20) U@@30) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@20))) (= (MapType0Select (|IMap#Elements| m@@25) u@@20) (MapType0Select (|IMap#Elements| |m'@@2|) u@@20)))
 :qid |DafnyPre.1307:35|
 :skolemid |615|
 :no-pattern (type u@@20)
 :no-pattern (U_2_int u@@20)
 :no-pattern (U_2_bool u@@20)
)))) (=> (and (forall ((u@@21 T@U) ) (!  (=> (= (type u@@21) U@@30) (and (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@21)) (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@21))) (=> (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@21)) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@21)))))
 :qid |DafnyPre.1306:36|
 :skolemid |614|
 :no-pattern (type u@@21)
 :no-pattern (U_2_int u@@21)
 :no-pattern (U_2_bool u@@21)
)) (forall ((u@@22 T@U) ) (!  (=> (and (= (type u@@22) U@@30) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@22))) (= (MapType0Select (|IMap#Elements| m@@25) u@@22) (MapType0Select (|IMap#Elements| |m'@@2|) u@@22)))
 :qid |DafnyPre.1307:35|
 :skolemid |615|
 :no-pattern (type u@@22)
 :no-pattern (U_2_int u@@22)
 :no-pattern (U_2_bool u@@22)
))) (|IMap#Equal| m@@25 |m'@@2|))))))
 :qid |DafnyPre.1304:21|
 :skolemid |616|
 :pattern ( (|IMap#Equal| m@@25 |m'@@2|))
)))
(assert (forall ((m@@26 T@U) (|m'@@3| T@U) ) (! (let ((V@@31 (IMapTypeInv1 (type m@@26))))
(let ((U@@31 (IMapTypeInv0 (type m@@26))))
 (=> (and (and (= (type m@@26) (IMapType U@@31 V@@31)) (= (type |m'@@3|) (IMapType U@@31 V@@31))) (|IMap#Equal| m@@26 |m'@@3|)) (= m@@26 |m'@@3|))))
 :qid |DafnyPre.1309:21|
 :skolemid |617|
 :pattern ( (|IMap#Equal| m@@26 |m'@@3|))
)))
(assert (forall ((x@@43 Int) (y@@12 Int) ) (! (= (INTERNAL_add_boogie x@@43 y@@12) (+ x@@43 y@@12))
 :qid |DafnyPre.1317:30|
 :skolemid |618|
 :pattern ( (INTERNAL_add_boogie x@@43 y@@12))
)))
(assert (forall ((x@@44 Int) (y@@13 Int) ) (! (= (INTERNAL_sub_boogie x@@44 y@@13) (- x@@44 y@@13))
 :qid |DafnyPre.1318:30|
 :skolemid |619|
 :pattern ( (INTERNAL_sub_boogie x@@44 y@@13))
)))
(assert (forall ((x@@45 Int) (y@@14 Int) ) (! (= (INTERNAL_mul_boogie x@@45 y@@14) (* x@@45 y@@14))
 :qid |DafnyPre.1319:30|
 :skolemid |620|
 :pattern ( (INTERNAL_mul_boogie x@@45 y@@14))
)))
(assert (forall ((x@@46 Int) (y@@15 Int) ) (! (= (INTERNAL_div_boogie x@@46 y@@15) (div x@@46 y@@15))
 :qid |DafnyPre.1320:30|
 :skolemid |621|
 :pattern ( (INTERNAL_div_boogie x@@46 y@@15))
)))
(assert (forall ((x@@47 Int) (y@@16 Int) ) (! (= (INTERNAL_mod_boogie x@@47 y@@16) (mod x@@47 y@@16))
 :qid |DafnyPre.1321:30|
 :skolemid |622|
 :pattern ( (INTERNAL_mod_boogie x@@47 y@@16))
)))
(assert (forall ((x@@48 Int) (y@@17 Int) ) (!  (and (=> (INTERNAL_lt_boogie x@@48 y@@17) (< x@@48 y@@17)) (=> (< x@@48 y@@17) (INTERNAL_lt_boogie x@@48 y@@17)))
 :qid |DafnyPre.1322:51|
 :skolemid |623|
 :pattern ( (INTERNAL_lt_boogie x@@48 y@@17))
)))
(assert (forall ((x@@49 Int) (y@@18 Int) ) (!  (and (=> (INTERNAL_le_boogie x@@49 y@@18) (<= x@@49 y@@18)) (=> (<= x@@49 y@@18) (INTERNAL_le_boogie x@@49 y@@18)))
 :qid |DafnyPre.1323:51|
 :skolemid |624|
 :pattern ( (INTERNAL_le_boogie x@@49 y@@18))
)))
(assert (forall ((x@@50 Int) (y@@19 Int) ) (!  (and (=> (INTERNAL_gt_boogie x@@50 y@@19) (> x@@50 y@@19)) (=> (> x@@50 y@@19) (INTERNAL_gt_boogie x@@50 y@@19)))
 :qid |DafnyPre.1324:51|
 :skolemid |625|
 :pattern ( (INTERNAL_gt_boogie x@@50 y@@19))
)))
(assert (forall ((x@@51 Int) (y@@20 Int) ) (!  (and (=> (INTERNAL_ge_boogie x@@51 y@@20) (>= x@@51 y@@20)) (=> (>= x@@51 y@@20) (INTERNAL_ge_boogie x@@51 y@@20)))
 :qid |DafnyPre.1325:51|
 :skolemid |626|
 :pattern ( (INTERNAL_ge_boogie x@@51 y@@20))
)))
(assert (forall ((x@@52 Int) (y@@21 Int) ) (! (= (Mul x@@52 y@@21) (* x@@52 y@@21))
 :qid |DafnyPre.1327:14|
 :skolemid |627|
 :pattern ( (Mul x@@52 y@@21))
)))
(assert (forall ((x@@53 Int) (y@@22 Int) ) (! (= (Div x@@53 y@@22) (div x@@53 y@@22))
 :qid |DafnyPre.1328:14|
 :skolemid |628|
 :pattern ( (Div x@@53 y@@22))
)))
(assert (forall ((x@@54 Int) (y@@23 Int) ) (! (= (Mod x@@54 y@@23) (mod x@@54 y@@23))
 :qid |DafnyPre.1329:14|
 :skolemid |629|
 :pattern ( (Mod x@@54 y@@23))
)))
(assert (forall ((x@@55 Int) (y@@24 Int) ) (! (= (Add x@@55 y@@24) (+ x@@55 y@@24))
 :qid |DafnyPre.1330:14|
 :skolemid |630|
 :pattern ( (Add x@@55 y@@24))
)))
(assert (forall ((x@@56 Int) (y@@25 Int) ) (! (= (Sub x@@56 y@@25) (- x@@56 y@@25))
 :qid |DafnyPre.1331:14|
 :skolemid |631|
 :pattern ( (Sub x@@56 y@@25))
)))
(assert (= (type Tclass._System.nat) TyType))
(assert (= (Tag Tclass._System.nat) Tagclass._System.nat))
(assert (forall ((bx@@34 T@U) ) (!  (=> (and (= (type bx@@34) BoxType) ($IsBox bx@@34 Tclass._System.nat)) (and (= ($Box ($Unbox intType bx@@34)) bx@@34) ($Is ($Unbox intType bx@@34) Tclass._System.nat)))
 :qid |unknown.0:0|
 :skolemid |632|
 :pattern ( ($IsBox bx@@34 Tclass._System.nat))
)))
(assert (forall ((|x#0| T@U) ) (!  (=> (= (type |x#0|) intType) (and (=> ($Is |x#0| Tclass._System.nat) (<= (LitInt 0) (U_2_int |x#0|))) (=> (<= (LitInt 0) (U_2_int |x#0|)) ($Is |x#0| Tclass._System.nat))))
 :qid |unknown.0:0|
 :skolemid |633|
 :pattern ( ($Is |x#0| Tclass._System.nat))
)))
(assert (forall ((|x#0@@0| T@U) ($h T@U) ) (!  (=> (and (= (type |x#0@@0|) intType) (= (type $h) (MapType0Type refType MapType1Type))) ($IsAlloc |x#0@@0| Tclass._System.nat $h))
 :qid |unknown.0:0|
 :skolemid |634|
 :pattern ( ($IsAlloc |x#0@@0| Tclass._System.nat $h))
)))
(assert (= (Tag Tclass._System.object?) Tagclass._System.object?))
(assert (forall ((bx@@35 T@U) ) (!  (=> (and (= (type bx@@35) BoxType) ($IsBox bx@@35 Tclass._System.object?)) (and (= ($Box ($Unbox refType bx@@35)) bx@@35) ($Is ($Unbox refType bx@@35) Tclass._System.object?)))
 :qid |unknown.0:0|
 :skolemid |635|
 :pattern ( ($IsBox bx@@35 Tclass._System.object?))
)))
(assert (forall (($o T@U) ) (!  (=> (= (type $o) refType) ($Is $o Tclass._System.object?))
 :qid |unknown.0:0|
 :skolemid |636|
 :pattern ( ($Is $o Tclass._System.object?))
)))
(assert (= (type null) refType))
(assert (forall (($o@@0 T@U) ($h@@0 T@U) ) (!  (=> (and (= (type $o@@0) refType) (= (type $h@@0) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc $o@@0 Tclass._System.object? $h@@0) (or (= $o@@0 null) (U_2_bool (MapType1Select (MapType0Select $h@@0 $o@@0) alloc)))) (=> (or (= $o@@0 null) (U_2_bool (MapType1Select (MapType0Select $h@@0 $o@@0) alloc))) ($IsAlloc $o@@0 Tclass._System.object? $h@@0))))
 :qid |unknown.0:0|
 :skolemid |637|
 :pattern ( ($IsAlloc $o@@0 Tclass._System.object? $h@@0))
)))
(assert (= (type Tclass._System.object) TyType))
(assert (= (Tag Tclass._System.object) Tagclass._System.object))
(assert (forall ((bx@@36 T@U) ) (!  (=> (and (= (type bx@@36) BoxType) ($IsBox bx@@36 Tclass._System.object)) (and (= ($Box ($Unbox refType bx@@36)) bx@@36) ($Is ($Unbox refType bx@@36) Tclass._System.object)))
 :qid |unknown.0:0|
 :skolemid |638|
 :pattern ( ($IsBox bx@@36 Tclass._System.object))
)))
(assert (forall ((|c#0| T@U) ) (!  (=> (= (type |c#0|) refType) (and (=> ($Is |c#0| Tclass._System.object) (and ($Is |c#0| Tclass._System.object?) (not (= |c#0| null)))) (=> (and ($Is |c#0| Tclass._System.object?) (not (= |c#0| null))) ($Is |c#0| Tclass._System.object))))
 :qid |unknown.0:0|
 :skolemid |639|
 :pattern ( ($Is |c#0| Tclass._System.object))
)))
(assert (forall ((|c#0@@0| T@U) ($h@@1 T@U) ) (!  (=> (and (= (type |c#0@@0|) refType) (= (type $h@@1) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |c#0@@0| Tclass._System.object $h@@1) ($IsAlloc |c#0@@0| Tclass._System.object? $h@@1)) (=> ($IsAlloc |c#0@@0| Tclass._System.object? $h@@1) ($IsAlloc |c#0@@0| Tclass._System.object $h@@1))))
 :qid |unknown.0:0|
 :skolemid |640|
 :pattern ( ($IsAlloc |c#0@@0| Tclass._System.object $h@@1))
)))
(assert (forall ((arg0@@107 T@U) ) (! (= (type (Tclass._System.array? arg0@@107)) TyType)
 :qid |funType:Tclass._System.array?|
 :pattern ( (Tclass._System.array? arg0@@107))
)))
(assert (forall ((|#$arg| T@U) ) (!  (=> (= (type |#$arg|) TyType) (= (Tag (Tclass._System.array? |#$arg|)) Tagclass._System.array?))
 :qid |unknown.0:0|
 :skolemid |641|
 :pattern ( (Tclass._System.array? |#$arg|))
)))
(assert (forall ((arg0@@108 T@U) ) (! (= (type (Tclass._System.array?_0 arg0@@108)) TyType)
 :qid |funType:Tclass._System.array?_0|
 :pattern ( (Tclass._System.array?_0 arg0@@108))
)))
(assert (forall ((|#$arg@@0| T@U) ) (!  (=> (= (type |#$arg@@0|) TyType) (= (Tclass._System.array?_0 (Tclass._System.array? |#$arg@@0|)) |#$arg@@0|))
 :qid |unknown.0:0|
 :skolemid |642|
 :pattern ( (Tclass._System.array? |#$arg@@0|))
)))
(assert (forall ((|#$arg@@1| T@U) (bx@@37 T@U) ) (!  (=> (and (and (= (type |#$arg@@1|) TyType) (= (type bx@@37) BoxType)) ($IsBox bx@@37 (Tclass._System.array? |#$arg@@1|))) (and (= ($Box ($Unbox refType bx@@37)) bx@@37) ($Is ($Unbox refType bx@@37) (Tclass._System.array? |#$arg@@1|))))
 :qid |unknown.0:0|
 :skolemid |643|
 :pattern ( ($IsBox bx@@37 (Tclass._System.array? |#$arg@@1|)))
)))
(assert (forall ((arg0@@109 T@U) ) (! (= (type (dtype arg0@@109)) TyType)
 :qid |funType:dtype|
 :pattern ( (dtype arg0@@109))
)))
(assert (forall ((|#$arg@@2| T@U) ($h@@2 T@U) ($o@@1 T@U) ($i0 Int) ) (!  (=> (and (and (and (= (type |#$arg@@2|) TyType) (= (type $h@@2) (MapType0Type refType MapType1Type))) (= (type $o@@1) refType)) (and (and ($IsGoodHeap $h@@2) (and (not (= $o@@1 null)) (= (dtype $o@@1) (Tclass._System.array? |#$arg@@2|)))) (and (<= 0 $i0) (< $i0 (_System.array.Length $o@@1))))) ($IsBox (MapType1Select (MapType0Select $h@@2 $o@@1) (IndexField $i0)) |#$arg@@2|))
 :qid |unknown.0:0|
 :skolemid |644|
 :pattern ( (MapType1Select (MapType0Select $h@@2 $o@@1) (IndexField $i0)) (Tclass._System.array? |#$arg@@2|))
)))
(assert (forall ((|#$arg@@3| T@U) ($h@@3 T@U) ($o@@2 T@U) ($i0@@0 Int) ) (!  (=> (and (and (= (type |#$arg@@3|) TyType) (= (type $h@@3) (MapType0Type refType MapType1Type))) (= (type $o@@2) refType)) (=> (and (and (and ($IsGoodHeap $h@@3) (and (not (= $o@@2 null)) (= (dtype $o@@2) (Tclass._System.array? |#$arg@@3|)))) (and (<= 0 $i0@@0) (< $i0@@0 (_System.array.Length $o@@2)))) (U_2_bool (MapType1Select (MapType0Select $h@@3 $o@@2) alloc))) ($IsAllocBox (MapType1Select (MapType0Select $h@@3 $o@@2) (IndexField $i0@@0)) |#$arg@@3| $h@@3)))
 :qid |unknown.0:0|
 :skolemid |645|
 :pattern ( (MapType1Select (MapType0Select $h@@3 $o@@2) (IndexField $i0@@0)) (Tclass._System.array? |#$arg@@3|))
)))
(assert (forall ((|#$arg@@4| T@U) ($o@@3 T@U) ) (!  (=> (and (= (type |#$arg@@4|) TyType) (= (type $o@@3) refType)) (and (=> ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)) (or (= $o@@3 null) (= (dtype $o@@3) (Tclass._System.array? |#$arg@@4|)))) (=> (or (= $o@@3 null) (= (dtype $o@@3) (Tclass._System.array? |#$arg@@4|))) ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)))))
 :qid |unknown.0:0|
 :skolemid |646|
 :pattern ( ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)))
)))
(assert (forall ((|#$arg@@5| T@U) ($o@@4 T@U) ($h@@4 T@U) ) (!  (=> (and (and (= (type |#$arg@@5|) TyType) (= (type $o@@4) refType)) (= (type $h@@4) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4) (or (= $o@@4 null) (U_2_bool (MapType1Select (MapType0Select $h@@4 $o@@4) alloc)))) (=> (or (= $o@@4 null) (U_2_bool (MapType1Select (MapType0Select $h@@4 $o@@4) alloc))) ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4))))
 :qid |unknown.0:0|
 :skolemid |647|
 :pattern ( ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4))
)))
(assert (forall ((|#$arg@@6| T@U) ($o@@5 T@U) ) (!  (=> (and (and (= (type |#$arg@@6|) TyType) (= (type $o@@5) refType)) (and (not (= $o@@5 null)) (= (dtype $o@@5) (Tclass._System.array? |#$arg@@6|)))) ($Is (int_2_U (_System.array.Length $o@@5)) TInt))
 :qid |unknown.0:0|
 :skolemid |648|
 :pattern ( (_System.array.Length $o@@5) (Tclass._System.array? |#$arg@@6|))
)))
(assert (forall ((|#$arg@@7| T@U) ($h@@5 T@U) ($o@@6 T@U) ) (!  (=> (and (and (and (= (type |#$arg@@7|) TyType) (= (type $h@@5) (MapType0Type refType MapType1Type))) (= (type $o@@6) refType)) (and (and ($IsGoodHeap $h@@5) (and (not (= $o@@6 null)) (= (dtype $o@@6) (Tclass._System.array? |#$arg@@7|)))) (U_2_bool (MapType1Select (MapType0Select $h@@5 $o@@6) alloc)))) ($IsAlloc (int_2_U (_System.array.Length $o@@6)) TInt $h@@5))
 :qid |unknown.0:0|
 :skolemid |649|
 :pattern ( (_System.array.Length $o@@6) (MapType1Select (MapType0Select $h@@5 $o@@6) alloc) (Tclass._System.array? |#$arg@@7|))
)))
(assert (forall ((arg0@@110 T@U) ) (! (= (type (Tclass._System.array arg0@@110)) TyType)
 :qid |funType:Tclass._System.array|
 :pattern ( (Tclass._System.array arg0@@110))
)))
(assert (forall ((_System.array$arg T@U) ) (!  (=> (= (type _System.array$arg) TyType) (= (Tag (Tclass._System.array _System.array$arg)) Tagclass._System.array))
 :qid |unknown.0:0|
 :skolemid |650|
 :pattern ( (Tclass._System.array _System.array$arg))
)))
(assert (forall ((arg0@@111 T@U) ) (! (= (type (Tclass._System.array_0 arg0@@111)) TyType)
 :qid |funType:Tclass._System.array_0|
 :pattern ( (Tclass._System.array_0 arg0@@111))
)))
(assert (forall ((_System.array$arg@@0 T@U) ) (!  (=> (= (type _System.array$arg@@0) TyType) (= (Tclass._System.array_0 (Tclass._System.array _System.array$arg@@0)) _System.array$arg@@0))
 :qid |unknown.0:0|
 :skolemid |651|
 :pattern ( (Tclass._System.array _System.array$arg@@0))
)))
(assert (forall ((_System.array$arg@@1 T@U) (bx@@38 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@1) TyType) (= (type bx@@38) BoxType)) ($IsBox bx@@38 (Tclass._System.array _System.array$arg@@1))) (and (= ($Box ($Unbox refType bx@@38)) bx@@38) ($Is ($Unbox refType bx@@38) (Tclass._System.array _System.array$arg@@1))))
 :qid |unknown.0:0|
 :skolemid |652|
 :pattern ( ($IsBox bx@@38 (Tclass._System.array _System.array$arg@@1)))
)))
(assert (forall ((_System.array$arg@@2 T@U) (|c#0@@1| T@U) ) (!  (=> (and (= (type _System.array$arg@@2) TyType) (= (type |c#0@@1|) refType)) (and (=> ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)) (and ($Is |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (not (= |c#0@@1| null)))) (=> (and ($Is |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (not (= |c#0@@1| null))) ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)))))
 :qid |unknown.0:0|
 :skolemid |653|
 :pattern ( ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)))
)))
(assert (forall ((_System.array$arg@@3 T@U) (|c#0@@2| T@U) ($h@@6 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@3) TyType) (= (type |c#0@@2|) refType)) (= (type $h@@6) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6) ($IsAlloc |c#0@@2| (Tclass._System.array? _System.array$arg@@3) $h@@6)) (=> ($IsAlloc |c#0@@2| (Tclass._System.array? _System.array$arg@@3) $h@@6) ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6))))
 :qid |unknown.0:0|
 :skolemid |654|
 :pattern ( ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6))
)))
(assert (forall ((arg0@@112 T@U) (arg1@@47 T@U) ) (! (= (type (Tclass._System.___hFunc1 arg0@@112 arg1@@47)) TyType)
 :qid |funType:Tclass._System.___hFunc1|
 :pattern ( (Tclass._System.___hFunc1 arg0@@112 arg1@@47))
)))
(assert (forall ((|#$T0| T@U) (|#$R| T@U) ) (!  (=> (and (= (type |#$T0|) TyType) (= (type |#$R|) TyType)) (= (Tag (Tclass._System.___hFunc1 |#$T0| |#$R|)) Tagclass._System.___hFunc1))
 :qid |unknown.0:0|
 :skolemid |655|
 :pattern ( (Tclass._System.___hFunc1 |#$T0| |#$R|))
)))
(assert (forall ((arg0@@113 T@U) ) (! (= (type (Tclass._System.___hFunc1_0 arg0@@113)) TyType)
 :qid |funType:Tclass._System.___hFunc1_0|
 :pattern ( (Tclass._System.___hFunc1_0 arg0@@113))
)))
(assert (forall ((|#$T0@@0| T@U) (|#$R@@0| T@U) ) (!  (=> (and (= (type |#$T0@@0|) TyType) (= (type |#$R@@0|) TyType)) (= (Tclass._System.___hFunc1_0 (Tclass._System.___hFunc1 |#$T0@@0| |#$R@@0|)) |#$T0@@0|))
 :qid |unknown.0:0|
 :skolemid |656|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@0| |#$R@@0|))
)))
(assert (forall ((arg0@@114 T@U) ) (! (= (type (Tclass._System.___hFunc1_1 arg0@@114)) TyType)
 :qid |funType:Tclass._System.___hFunc1_1|
 :pattern ( (Tclass._System.___hFunc1_1 arg0@@114))
)))
(assert (forall ((|#$T0@@1| T@U) (|#$R@@1| T@U) ) (!  (=> (and (= (type |#$T0@@1|) TyType) (= (type |#$R@@1|) TyType)) (= (Tclass._System.___hFunc1_1 (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@1|)) |#$R@@1|))
 :qid |unknown.0:0|
 :skolemid |657|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@1|))
)))
(assert (forall ((|#$T0@@2| T@U) (|#$R@@2| T@U) (bx@@39 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@2|) TyType) (= (type |#$R@@2|) TyType)) (= (type bx@@39) BoxType)) ($IsBox bx@@39 (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|))) (and (= ($Box ($Unbox HandleTypeType bx@@39)) bx@@39) ($Is ($Unbox HandleTypeType bx@@39) (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|))))
 :qid |unknown.0:0|
 :skolemid |658|
 :pattern ( ($IsBox bx@@39 (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|)))
)))
(assert  (and (and (and (and (and (and (and (and (forall ((arg0@@115 T@T) (arg1@@48 T@T) (arg2@@8 T@T) ) (! (= (Ctor (MapType2Type arg0@@115 arg1@@48 arg2@@8)) 23)
 :qid |ctor:MapType2Type|
)) (forall ((arg0@@116 T@T) (arg1@@49 T@T) (arg2@@9 T@T) ) (! (= (MapType2TypeInv0 (MapType2Type arg0@@116 arg1@@49 arg2@@9)) arg0@@116)
 :qid |typeInv:MapType2TypeInv0|
 :pattern ( (MapType2Type arg0@@116 arg1@@49 arg2@@9))
))) (forall ((arg0@@117 T@T) (arg1@@50 T@T) (arg2@@10 T@T) ) (! (= (MapType2TypeInv1 (MapType2Type arg0@@117 arg1@@50 arg2@@10)) arg1@@50)
 :qid |typeInv:MapType2TypeInv1|
 :pattern ( (MapType2Type arg0@@117 arg1@@50 arg2@@10))
))) (forall ((arg0@@118 T@T) (arg1@@51 T@T) (arg2@@11 T@T) ) (! (= (MapType2TypeInv2 (MapType2Type arg0@@118 arg1@@51 arg2@@11)) arg2@@11)
 :qid |typeInv:MapType2TypeInv2|
 :pattern ( (MapType2Type arg0@@118 arg1@@51 arg2@@11))
))) (forall ((arg0@@119 T@U) (arg1@@52 T@U) (arg2@@12 T@U) ) (! (let ((aVar2 (MapType2TypeInv2 (type arg0@@119))))
(= (type (MapType2Select arg0@@119 arg1@@52 arg2@@12)) aVar2))
 :qid |funType:MapType2Select|
 :pattern ( (MapType2Select arg0@@119 arg1@@52 arg2@@12))
))) (forall ((arg0@@120 T@U) (arg1@@53 T@U) (arg2@@13 T@U) (arg3@@1 T@U) ) (! (let ((aVar2@@0 (type arg3@@1)))
(let ((aVar1@@2 (type arg2@@13)))
(let ((aVar0@@0 (type arg1@@53)))
(= (type (MapType2Store arg0@@120 arg1@@53 arg2@@13 arg3@@1)) (MapType2Type aVar0@@0 aVar1@@2 aVar2@@0)))))
 :qid |funType:MapType2Store|
 :pattern ( (MapType2Store arg0@@120 arg1@@53 arg2@@13 arg3@@1))
))) (forall ((m@@27 T@U) (x0@@5 T@U) (x1 T@U) (val@@6 T@U) ) (! (let ((aVar2@@1 (MapType2TypeInv2 (type m@@27))))
 (=> (= (type val@@6) aVar2@@1) (= (MapType2Select (MapType2Store m@@27 x0@@5 x1 val@@6) x0@@5 x1) val@@6)))
 :qid |mapAx0:MapType2Select|
 :weight 0
))) (and (and (forall ((val@@7 T@U) (m@@28 T@U) (x0@@6 T@U) (x1@@0 T@U) (y0@@3 T@U) (y1 T@U) ) (!  (or (= x0@@6 y0@@3) (= (MapType2Select (MapType2Store m@@28 x0@@6 x1@@0 val@@7) y0@@3 y1) (MapType2Select m@@28 y0@@3 y1)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
)) (forall ((val@@8 T@U) (m@@29 T@U) (x0@@7 T@U) (x1@@1 T@U) (y0@@4 T@U) (y1@@0 T@U) ) (!  (or (= x1@@1 y1@@0) (= (MapType2Select (MapType2Store m@@29 x0@@7 x1@@1 val@@8) y0@@4 y1@@0) (MapType2Select m@@29 y0@@4 y1@@0)))
 :qid |mapAx1:MapType2Select:1|
 :weight 0
))) (forall ((val@@9 T@U) (m@@30 T@U) (x0@@8 T@U) (x1@@2 T@U) (y0@@5 T@U) (y1@@1 T@U) ) (!  (or true (= (MapType2Select (MapType2Store m@@30 x0@@8 x1@@2 val@@9) y0@@5 y1@@1) (MapType2Select m@@30 y0@@5 y1@@1)))
 :qid |mapAx2:MapType2Select|
 :weight 0
)))) (forall ((arg0@@121 T@U) (arg1@@54 T@U) (arg2@@14 T@U) ) (! (= (type (Handle1 arg0@@121 arg1@@54 arg2@@14)) HandleTypeType)
 :qid |funType:Handle1|
 :pattern ( (Handle1 arg0@@121 arg1@@54 arg2@@14))
))))
(assert (forall ((t0@@12 T@U) (t1@@3 T@U) (heap@@1 T@U) (h@@20 T@U) (r@@6 T@U) (rd T@U) (bx0 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@12) TyType) (= (type t1@@3) TyType)) (= (type heap@@1) (MapType0Type refType MapType1Type))) (= (type h@@20) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@6) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0) BoxType)) (= (Apply1 t0@@12 t1@@3 heap@@1 (Handle1 h@@20 r@@6 rd) bx0) (MapType2Select h@@20 heap@@1 bx0)))
 :qid |unknown.0:0|
 :skolemid |659|
 :pattern ( (Apply1 t0@@12 t1@@3 heap@@1 (Handle1 h@@20 r@@6 rd) bx0))
)))
(assert (forall ((t0@@13 T@U) (t1@@4 T@U) (heap@@2 T@U) (h@@21 T@U) (r@@7 T@U) (rd@@0 T@U) (bx0@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@13) TyType) (= (type t1@@4) TyType)) (= (type heap@@2) (MapType0Type refType MapType1Type))) (= (type h@@21) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@7) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd@@0) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@0) BoxType)) (U_2_bool (MapType2Select r@@7 heap@@2 bx0@@0))) (Requires1 t0@@13 t1@@4 heap@@2 (Handle1 h@@21 r@@7 rd@@0) bx0@@0))
 :qid |unknown.0:0|
 :skolemid |660|
 :pattern ( (Requires1 t0@@13 t1@@4 heap@@2 (Handle1 h@@21 r@@7 rd@@0) bx0@@0))
)))
(assert (forall ((arg0@@122 T@U) (arg1@@55 T@U) (arg2@@15 T@U) (arg3@@2 T@U) (arg4@@0 T@U) ) (! (= (type (Reads1 arg0@@122 arg1@@55 arg2@@15 arg3@@2 arg4@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads1|
 :pattern ( (Reads1 arg0@@122 arg1@@55 arg2@@15 arg3@@2 arg4@@0))
)))
(assert (forall ((t0@@14 T@U) (t1@@5 T@U) (heap@@3 T@U) (h@@22 T@U) (r@@8 T@U) (rd@@1 T@U) (bx0@@1 T@U) (bx@@40 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@14) TyType) (= (type t1@@5) TyType)) (= (type heap@@3) (MapType0Type refType MapType1Type))) (= (type h@@22) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@8) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd@@1) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@1) BoxType)) (= (type bx@@40) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads1 t0@@14 t1@@5 heap@@3 (Handle1 h@@22 r@@8 rd@@1) bx0@@1) bx@@40)) (U_2_bool (MapType0Select (MapType2Select rd@@1 heap@@3 bx0@@1) bx@@40))) (=> (U_2_bool (MapType0Select (MapType2Select rd@@1 heap@@3 bx0@@1) bx@@40)) (U_2_bool (MapType0Select (Reads1 t0@@14 t1@@5 heap@@3 (Handle1 h@@22 r@@8 rd@@1) bx0@@1) bx@@40)))))
 :qid |unknown.0:0|
 :skolemid |661|
 :pattern ( (MapType0Select (Reads1 t0@@14 t1@@5 heap@@3 (Handle1 h@@22 r@@8 rd@@1) bx0@@1) bx@@40))
)))
(assert (forall ((t0@@15 T@U) (t1@@6 T@U) (h0@@0 T@U) (h1@@0 T@U) (f@@5 T@U) (bx0@@2 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@15) TyType) (= (type t1@@6) TyType)) (= (type h0@@0) (MapType0Type refType MapType1Type))) (= (type h1@@0) (MapType0Type refType MapType1Type))) (= (type f@@5) HandleTypeType)) (= (type bx0@@2) BoxType)) (and (and (and ($HeapSucc h0@@0 h1@@0) (and ($IsGoodHeap h0@@0) ($IsGoodHeap h1@@0))) (and ($IsBox bx0@@2 t0@@15) ($Is f@@5 (Tclass._System.___hFunc1 t0@@15 t1@@6)))) (forall ((o@@54 T@U) (fld T@U) ) (! (let ((a@@79 (FieldTypeInv0 (type fld))))
 (=> (and (and (= (type o@@54) refType) (= (type fld) (FieldType a@@79))) (and (not (= o@@54 null)) (U_2_bool (MapType0Select (Reads1 t0@@15 t1@@6 h0@@0 f@@5 bx0@@2) ($Box o@@54))))) (= (MapType1Select (MapType0Select h0@@0 o@@54) fld) (MapType1Select (MapType0Select h1@@0 o@@54) fld))))
 :qid |unknown.0:0|
 :skolemid |662|
 :no-pattern (type o@@54)
 :no-pattern (type fld)
 :no-pattern (U_2_int o@@54)
 :no-pattern (U_2_bool o@@54)
 :no-pattern (U_2_int fld)
 :no-pattern (U_2_bool fld)
)))) (= (Reads1 t0@@15 t1@@6 h0@@0 f@@5 bx0@@2) (Reads1 t0@@15 t1@@6 h1@@0 f@@5 bx0@@2)))
 :qid |unknown.0:0|
 :skolemid |663|
 :pattern ( ($HeapSucc h0@@0 h1@@0) (Reads1 t0@@15 t1@@6 h1@@0 f@@5 bx0@@2))
)))
(assert (forall ((t0@@16 T@U) (t1@@7 T@U) (h0@@1 T@U) (h1@@1 T@U) (f@@6 T@U) (bx0@@3 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@16) TyType) (= (type t1@@7) TyType)) (= (type h0@@1) (MapType0Type refType MapType1Type))) (= (type h1@@1) (MapType0Type refType MapType1Type))) (= (type f@@6) HandleTypeType)) (= (type bx0@@3) BoxType)) (and (and (and ($HeapSucc h0@@1 h1@@1) (and ($IsGoodHeap h0@@1) ($IsGoodHeap h1@@1))) (and ($IsBox bx0@@3 t0@@16) ($Is f@@6 (Tclass._System.___hFunc1 t0@@16 t1@@7)))) (forall ((o@@55 T@U) (fld@@0 T@U) ) (! (let ((a@@80 (FieldTypeInv0 (type fld@@0))))
 (=> (and (and (= (type o@@55) refType) (= (type fld@@0) (FieldType a@@80))) (and (not (= o@@55 null)) (U_2_bool (MapType0Select (Reads1 t0@@16 t1@@7 h1@@1 f@@6 bx0@@3) ($Box o@@55))))) (= (MapType1Select (MapType0Select h0@@1 o@@55) fld@@0) (MapType1Select (MapType0Select h1@@1 o@@55) fld@@0))))
 :qid |unknown.0:0|
 :skolemid |664|
 :no-pattern (type o@@55)
 :no-pattern (type fld@@0)
 :no-pattern (U_2_int o@@55)
 :no-pattern (U_2_bool o@@55)
 :no-pattern (U_2_int fld@@0)
 :no-pattern (U_2_bool fld@@0)
)))) (= (Reads1 t0@@16 t1@@7 h0@@1 f@@6 bx0@@3) (Reads1 t0@@16 t1@@7 h1@@1 f@@6 bx0@@3)))
 :qid |unknown.0:0|
 :skolemid |665|
 :pattern ( ($HeapSucc h0@@1 h1@@1) (Reads1 t0@@16 t1@@7 h1@@1 f@@6 bx0@@3))
)))
(assert (forall ((t0@@17 T@U) (t1@@8 T@U) (h0@@2 T@U) (h1@@2 T@U) (f@@7 T@U) (bx0@@4 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@17) TyType) (= (type t1@@8) TyType)) (= (type h0@@2) (MapType0Type refType MapType1Type))) (= (type h1@@2) (MapType0Type refType MapType1Type))) (= (type f@@7) HandleTypeType)) (= (type bx0@@4) BoxType)) (and (and (and ($HeapSucc h0@@2 h1@@2) (and ($IsGoodHeap h0@@2) ($IsGoodHeap h1@@2))) (and ($IsBox bx0@@4 t0@@17) ($Is f@@7 (Tclass._System.___hFunc1 t0@@17 t1@@8)))) (forall ((o@@56 T@U) (fld@@1 T@U) ) (! (let ((a@@81 (FieldTypeInv0 (type fld@@1))))
 (=> (and (and (= (type o@@56) refType) (= (type fld@@1) (FieldType a@@81))) (and (not (= o@@56 null)) (U_2_bool (MapType0Select (Reads1 t0@@17 t1@@8 h0@@2 f@@7 bx0@@4) ($Box o@@56))))) (= (MapType1Select (MapType0Select h0@@2 o@@56) fld@@1) (MapType1Select (MapType0Select h1@@2 o@@56) fld@@1))))
 :qid |unknown.0:0|
 :skolemid |666|
 :no-pattern (type o@@56)
 :no-pattern (type fld@@1)
 :no-pattern (U_2_int o@@56)
 :no-pattern (U_2_bool o@@56)
 :no-pattern (U_2_int fld@@1)
 :no-pattern (U_2_bool fld@@1)
)))) (and (=> (Requires1 t0@@17 t1@@8 h0@@2 f@@7 bx0@@4) (Requires1 t0@@17 t1@@8 h1@@2 f@@7 bx0@@4)) (=> (Requires1 t0@@17 t1@@8 h1@@2 f@@7 bx0@@4) (Requires1 t0@@17 t1@@8 h0@@2 f@@7 bx0@@4))))
 :qid |unknown.0:0|
 :skolemid |667|
 :pattern ( ($HeapSucc h0@@2 h1@@2) (Requires1 t0@@17 t1@@8 h1@@2 f@@7 bx0@@4))
)))
(assert (forall ((t0@@18 T@U) (t1@@9 T@U) (h0@@3 T@U) (h1@@3 T@U) (f@@8 T@U) (bx0@@5 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@18) TyType) (= (type t1@@9) TyType)) (= (type h0@@3) (MapType0Type refType MapType1Type))) (= (type h1@@3) (MapType0Type refType MapType1Type))) (= (type f@@8) HandleTypeType)) (= (type bx0@@5) BoxType)) (and (and (and ($HeapSucc h0@@3 h1@@3) (and ($IsGoodHeap h0@@3) ($IsGoodHeap h1@@3))) (and ($IsBox bx0@@5 t0@@18) ($Is f@@8 (Tclass._System.___hFunc1 t0@@18 t1@@9)))) (forall ((o@@57 T@U) (fld@@2 T@U) ) (! (let ((a@@82 (FieldTypeInv0 (type fld@@2))))
 (=> (and (and (= (type o@@57) refType) (= (type fld@@2) (FieldType a@@82))) (and (not (= o@@57 null)) (U_2_bool (MapType0Select (Reads1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5) ($Box o@@57))))) (= (MapType1Select (MapType0Select h0@@3 o@@57) fld@@2) (MapType1Select (MapType0Select h1@@3 o@@57) fld@@2))))
 :qid |unknown.0:0|
 :skolemid |668|
 :no-pattern (type o@@57)
 :no-pattern (type fld@@2)
 :no-pattern (U_2_int o@@57)
 :no-pattern (U_2_bool o@@57)
 :no-pattern (U_2_int fld@@2)
 :no-pattern (U_2_bool fld@@2)
)))) (and (=> (Requires1 t0@@18 t1@@9 h0@@3 f@@8 bx0@@5) (Requires1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5)) (=> (Requires1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5) (Requires1 t0@@18 t1@@9 h0@@3 f@@8 bx0@@5))))
 :qid |unknown.0:0|
 :skolemid |669|
 :pattern ( ($HeapSucc h0@@3 h1@@3) (Requires1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5))
)))
(assert (forall ((t0@@19 T@U) (t1@@10 T@U) (h0@@4 T@U) (h1@@4 T@U) (f@@9 T@U) (bx0@@6 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@19) TyType) (= (type t1@@10) TyType)) (= (type h0@@4) (MapType0Type refType MapType1Type))) (= (type h1@@4) (MapType0Type refType MapType1Type))) (= (type f@@9) HandleTypeType)) (= (type bx0@@6) BoxType)) (and (and (and ($HeapSucc h0@@4 h1@@4) (and ($IsGoodHeap h0@@4) ($IsGoodHeap h1@@4))) (and ($IsBox bx0@@6 t0@@19) ($Is f@@9 (Tclass._System.___hFunc1 t0@@19 t1@@10)))) (forall ((o@@58 T@U) (fld@@3 T@U) ) (! (let ((a@@83 (FieldTypeInv0 (type fld@@3))))
 (=> (and (and (= (type o@@58) refType) (= (type fld@@3) (FieldType a@@83))) (and (not (= o@@58 null)) (U_2_bool (MapType0Select (Reads1 t0@@19 t1@@10 h0@@4 f@@9 bx0@@6) ($Box o@@58))))) (= (MapType1Select (MapType0Select h0@@4 o@@58) fld@@3) (MapType1Select (MapType0Select h1@@4 o@@58) fld@@3))))
 :qid |unknown.0:0|
 :skolemid |670|
 :no-pattern (type o@@58)
 :no-pattern (type fld@@3)
 :no-pattern (U_2_int o@@58)
 :no-pattern (U_2_bool o@@58)
 :no-pattern (U_2_int fld@@3)
 :no-pattern (U_2_bool fld@@3)
)))) (= (Apply1 t0@@19 t1@@10 h0@@4 f@@9 bx0@@6) (Apply1 t0@@19 t1@@10 h1@@4 f@@9 bx0@@6)))
 :qid |unknown.0:0|
 :skolemid |671|
 :pattern ( ($HeapSucc h0@@4 h1@@4) (Apply1 t0@@19 t1@@10 h1@@4 f@@9 bx0@@6))
)))
(assert (forall ((t0@@20 T@U) (t1@@11 T@U) (h0@@5 T@U) (h1@@5 T@U) (f@@10 T@U) (bx0@@7 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@20) TyType) (= (type t1@@11) TyType)) (= (type h0@@5) (MapType0Type refType MapType1Type))) (= (type h1@@5) (MapType0Type refType MapType1Type))) (= (type f@@10) HandleTypeType)) (= (type bx0@@7) BoxType)) (and (and (and ($HeapSucc h0@@5 h1@@5) (and ($IsGoodHeap h0@@5) ($IsGoodHeap h1@@5))) (and ($IsBox bx0@@7 t0@@20) ($Is f@@10 (Tclass._System.___hFunc1 t0@@20 t1@@11)))) (forall ((o@@59 T@U) (fld@@4 T@U) ) (! (let ((a@@84 (FieldTypeInv0 (type fld@@4))))
 (=> (and (and (= (type o@@59) refType) (= (type fld@@4) (FieldType a@@84))) (and (not (= o@@59 null)) (U_2_bool (MapType0Select (Reads1 t0@@20 t1@@11 h1@@5 f@@10 bx0@@7) ($Box o@@59))))) (= (MapType1Select (MapType0Select h0@@5 o@@59) fld@@4) (MapType1Select (MapType0Select h1@@5 o@@59) fld@@4))))
 :qid |unknown.0:0|
 :skolemid |672|
 :no-pattern (type o@@59)
 :no-pattern (type fld@@4)
 :no-pattern (U_2_int o@@59)
 :no-pattern (U_2_bool o@@59)
 :no-pattern (U_2_int fld@@4)
 :no-pattern (U_2_bool fld@@4)
)))) (= (Apply1 t0@@20 t1@@11 h0@@5 f@@10 bx0@@7) (Apply1 t0@@20 t1@@11 h1@@5 f@@10 bx0@@7)))
 :qid |unknown.0:0|
 :skolemid |673|
 :pattern ( ($HeapSucc h0@@5 h1@@5) (Apply1 t0@@20 t1@@11 h1@@5 f@@10 bx0@@7))
)))
(assert (forall ((t0@@21 T@U) (t1@@12 T@U) (heap@@4 T@U) (f@@11 T@U) (bx0@@8 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@21) TyType) (= (type t1@@12) TyType)) (= (type heap@@4) (MapType0Type refType MapType1Type))) (= (type f@@11) HandleTypeType)) (= (type bx0@@8) BoxType)) (and ($IsGoodHeap heap@@4) (and ($IsBox bx0@@8 t0@@21) ($Is f@@11 (Tclass._System.___hFunc1 t0@@21 t1@@12))))) (and (=> (|Set#Equal| (Reads1 t0@@21 t1@@12 $OneHeap f@@11 bx0@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads1 t0@@21 t1@@12 heap@@4 f@@11 bx0@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads1 t0@@21 t1@@12 heap@@4 f@@11 bx0@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads1 t0@@21 t1@@12 $OneHeap f@@11 bx0@@8) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |674|
 :pattern ( (Reads1 t0@@21 t1@@12 $OneHeap f@@11 bx0@@8) ($IsGoodHeap heap@@4))
 :pattern ( (Reads1 t0@@21 t1@@12 heap@@4 f@@11 bx0@@8))
)))
(assert (forall ((t0@@22 T@U) (t1@@13 T@U) (heap@@5 T@U) (f@@12 T@U) (bx0@@9 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@22) TyType) (= (type t1@@13) TyType)) (= (type heap@@5) (MapType0Type refType MapType1Type))) (= (type f@@12) HandleTypeType)) (= (type bx0@@9) BoxType)) (and (and ($IsGoodHeap heap@@5) (and ($IsBox bx0@@9 t0@@22) ($Is f@@12 (Tclass._System.___hFunc1 t0@@22 t1@@13)))) (|Set#Equal| (Reads1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9) (|Set#Empty| BoxType)))) (and (=> (Requires1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9) (Requires1 t0@@22 t1@@13 heap@@5 f@@12 bx0@@9)) (=> (Requires1 t0@@22 t1@@13 heap@@5 f@@12 bx0@@9) (Requires1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9))))
 :qid |unknown.0:0|
 :skolemid |675|
 :pattern ( (Requires1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9) ($IsGoodHeap heap@@5))
 :pattern ( (Requires1 t0@@22 t1@@13 heap@@5 f@@12 bx0@@9))
)))
(assert (forall ((f@@13 T@U) (t0@@23 T@U) (t1@@14 T@U) ) (!  (=> (and (and (= (type f@@13) HandleTypeType) (= (type t0@@23) TyType)) (= (type t1@@14) TyType)) (and (=> ($Is f@@13 (Tclass._System.___hFunc1 t0@@23 t1@@14)) (forall ((h@@23 T@U) (bx0@@10 T@U) ) (!  (=> (and (= (type h@@23) (MapType0Type refType MapType1Type)) (= (type bx0@@10) BoxType)) (=> (and (and ($IsGoodHeap h@@23) ($IsBox bx0@@10 t0@@23)) (Requires1 t0@@23 t1@@14 h@@23 f@@13 bx0@@10)) ($IsBox (Apply1 t0@@23 t1@@14 h@@23 f@@13 bx0@@10) t1@@14)))
 :qid |DafnyPre.515:12|
 :skolemid |676|
 :pattern ( (Apply1 t0@@23 t1@@14 h@@23 f@@13 bx0@@10))
))) (=> (forall ((h@@24 T@U) (bx0@@11 T@U) ) (!  (=> (and (= (type h@@24) (MapType0Type refType MapType1Type)) (= (type bx0@@11) BoxType)) (=> (and (and ($IsGoodHeap h@@24) ($IsBox bx0@@11 t0@@23)) (Requires1 t0@@23 t1@@14 h@@24 f@@13 bx0@@11)) ($IsBox (Apply1 t0@@23 t1@@14 h@@24 f@@13 bx0@@11) t1@@14)))
 :qid |DafnyPre.515:12|
 :skolemid |676|
 :pattern ( (Apply1 t0@@23 t1@@14 h@@24 f@@13 bx0@@11))
)) ($Is f@@13 (Tclass._System.___hFunc1 t0@@23 t1@@14)))))
 :qid |unknown.0:0|
 :skolemid |677|
 :pattern ( ($Is f@@13 (Tclass._System.___hFunc1 t0@@23 t1@@14)))
)))
(assert (forall ((f@@14 T@U) (t0@@24 T@U) (t1@@15 T@U) (u0 T@U) (u1 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@14) HandleTypeType) (= (type t0@@24) TyType)) (= (type t1@@15) TyType)) (= (type u0) TyType)) (= (type u1) TyType)) (and (and ($Is f@@14 (Tclass._System.___hFunc1 t0@@24 t1@@15)) (forall ((bx@@41 T@U) ) (!  (=> (and (= (type bx@@41) BoxType) ($IsBox bx@@41 u0)) ($IsBox bx@@41 t0@@24))
 :qid |unknown.0:0|
 :skolemid |678|
 :pattern ( ($IsBox bx@@41 u0))
 :pattern ( ($IsBox bx@@41 t0@@24))
))) (forall ((bx@@42 T@U) ) (!  (=> (and (= (type bx@@42) BoxType) ($IsBox bx@@42 t1@@15)) ($IsBox bx@@42 u1))
 :qid |unknown.0:0|
 :skolemid |679|
 :pattern ( ($IsBox bx@@42 t1@@15))
 :pattern ( ($IsBox bx@@42 u1))
)))) ($Is f@@14 (Tclass._System.___hFunc1 u0 u1)))
 :qid |unknown.0:0|
 :skolemid |680|
 :pattern ( ($Is f@@14 (Tclass._System.___hFunc1 t0@@24 t1@@15)) ($Is f@@14 (Tclass._System.___hFunc1 u0 u1)))
)))
(assert (forall ((f@@15 T@U) (t0@@25 T@U) (t1@@16 T@U) (h@@25 T@U) ) (!  (=> (and (and (and (and (= (type f@@15) HandleTypeType) (= (type t0@@25) TyType)) (= (type t1@@16) TyType)) (= (type h@@25) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@25)) (and (=> ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@25 t1@@16) h@@25) (forall ((bx0@@12 T@U) ) (!  (=> (= (type bx0@@12) BoxType) (=> (and (and ($IsBox bx0@@12 t0@@25) ($IsAllocBox bx0@@12 t0@@25 h@@25)) (Requires1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12)) (forall ((r@@9 T@U) ) (!  (=> (= (type r@@9) refType) (=> (and (not (= r@@9 null)) (U_2_bool (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12) ($Box r@@9)))) (U_2_bool (MapType1Select (MapType0Select h@@25 r@@9) alloc))))
 :qid |unknown.0:0|
 :skolemid |681|
 :pattern ( (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12) ($Box r@@9)))
))))
 :qid |unknown.0:0|
 :skolemid |682|
 :pattern ( (Apply1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12))
 :pattern ( (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12))
))) (=> (forall ((bx0@@13 T@U) ) (!  (=> (= (type bx0@@13) BoxType) (=> (and (and ($IsBox bx0@@13 t0@@25) ($IsAllocBox bx0@@13 t0@@25 h@@25)) (Requires1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13)) (forall ((r@@10 T@U) ) (!  (=> (= (type r@@10) refType) (=> (and (not (= r@@10 null)) (U_2_bool (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13) ($Box r@@10)))) (U_2_bool (MapType1Select (MapType0Select h@@25 r@@10) alloc))))
 :qid |unknown.0:0|
 :skolemid |681|
 :pattern ( (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13) ($Box r@@10)))
))))
 :qid |unknown.0:0|
 :skolemid |682|
 :pattern ( (Apply1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13))
 :pattern ( (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13))
)) ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@25 t1@@16) h@@25))))
 :qid |unknown.0:0|
 :skolemid |683|
 :pattern ( ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@25 t1@@16) h@@25))
)))
(assert (forall ((f@@16 T@U) (t0@@26 T@U) (t1@@17 T@U) (h@@26 T@U) ) (!  (=> (and (and (and (and (= (type f@@16) HandleTypeType) (= (type t0@@26) TyType)) (= (type t1@@17) TyType)) (= (type h@@26) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@26) ($IsAlloc f@@16 (Tclass._System.___hFunc1 t0@@26 t1@@17) h@@26))) (forall ((bx0@@14 T@U) ) (!  (=> (= (type bx0@@14) BoxType) (=> (and ($IsAllocBox bx0@@14 t0@@26 h@@26) (Requires1 t0@@26 t1@@17 h@@26 f@@16 bx0@@14)) ($IsAllocBox (Apply1 t0@@26 t1@@17 h@@26 f@@16 bx0@@14) t1@@17 h@@26)))
 :qid |unknown.0:0|
 :skolemid |684|
 :pattern ( (Apply1 t0@@26 t1@@17 h@@26 f@@16 bx0@@14))
)))
 :qid |unknown.0:0|
 :skolemid |685|
 :pattern ( ($IsAlloc f@@16 (Tclass._System.___hFunc1 t0@@26 t1@@17) h@@26))
)))
(assert (forall ((arg0@@123 T@U) (arg1@@56 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1 arg0@@123 arg1@@56)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1|
 :pattern ( (Tclass._System.___hPartialFunc1 arg0@@123 arg1@@56))
)))
(assert (forall ((|#$T0@@3| T@U) (|#$R@@3| T@U) ) (!  (=> (and (= (type |#$T0@@3|) TyType) (= (type |#$R@@3|) TyType)) (= (Tag (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@3|)) Tagclass._System.___hPartialFunc1))
 :qid |unknown.0:0|
 :skolemid |686|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@3|))
)))
(assert (forall ((arg0@@124 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_0 arg0@@124)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_0|
 :pattern ( (Tclass._System.___hPartialFunc1_0 arg0@@124))
)))
(assert (forall ((|#$T0@@4| T@U) (|#$R@@4| T@U) ) (!  (=> (and (= (type |#$T0@@4|) TyType) (= (type |#$R@@4|) TyType)) (= (Tclass._System.___hPartialFunc1_0 (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@4|)) |#$T0@@4|))
 :qid |unknown.0:0|
 :skolemid |687|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@4|))
)))
(assert (forall ((arg0@@125 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_1 arg0@@125)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_1|
 :pattern ( (Tclass._System.___hPartialFunc1_1 arg0@@125))
)))
(assert (forall ((|#$T0@@5| T@U) (|#$R@@5| T@U) ) (!  (=> (and (= (type |#$T0@@5|) TyType) (= (type |#$R@@5|) TyType)) (= (Tclass._System.___hPartialFunc1_1 (Tclass._System.___hPartialFunc1 |#$T0@@5| |#$R@@5|)) |#$R@@5|))
 :qid |unknown.0:0|
 :skolemid |688|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@5| |#$R@@5|))
)))
(assert (forall ((|#$T0@@6| T@U) (|#$R@@6| T@U) (bx@@43 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@6|) TyType) (= (type |#$R@@6|) TyType)) (= (type bx@@43) BoxType)) ($IsBox bx@@43 (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|))) (and (= ($Box ($Unbox HandleTypeType bx@@43)) bx@@43) ($Is ($Unbox HandleTypeType bx@@43) (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|))))
 :qid |unknown.0:0|
 :skolemid |689|
 :pattern ( ($IsBox bx@@43 (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|)))
)))
(assert (forall ((|#$T0@@7| T@U) (|#$R@@7| T@U) (|f#0| T@U) ) (!  (=> (and (and (= (type |#$T0@@7|) TyType) (= (type |#$R@@7|) TyType)) (= (type |f#0|) HandleTypeType)) (and (=> ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|)) (and ($Is |f#0| (Tclass._System.___hFunc1 |#$T0@@7| |#$R@@7|)) (forall ((|x0#0| T@U) ) (!  (=> (and (= (type |x0#0|) BoxType) ($IsBox |x0#0| |#$T0@@7|)) (|Set#Equal| (Reads1 |#$T0@@7| |#$R@@7| $OneHeap |f#0| |x0#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |690|
 :no-pattern (type |x0#0|)
 :no-pattern (U_2_int |x0#0|)
 :no-pattern (U_2_bool |x0#0|)
)))) (=> (and ($Is |f#0| (Tclass._System.___hFunc1 |#$T0@@7| |#$R@@7|)) (forall ((|x0#0@@0| T@U) ) (!  (=> (and (= (type |x0#0@@0|) BoxType) ($IsBox |x0#0@@0| |#$T0@@7|)) (|Set#Equal| (Reads1 |#$T0@@7| |#$R@@7| $OneHeap |f#0| |x0#0@@0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |690|
 :no-pattern (type |x0#0@@0|)
 :no-pattern (U_2_int |x0#0@@0|)
 :no-pattern (U_2_bool |x0#0@@0|)
))) ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|)))))
 :qid |unknown.0:0|
 :skolemid |691|
 :pattern ( ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|)))
)))
(assert (forall ((|#$T0@@8| T@U) (|#$R@@8| T@U) (|f#0@@0| T@U) ($h@@7 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@8|) TyType) (= (type |#$R@@8|) TyType)) (= (type |f#0@@0|) HandleTypeType)) (= (type $h@@7) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7) ($IsAlloc |f#0@@0| (Tclass._System.___hFunc1 |#$T0@@8| |#$R@@8|) $h@@7)) (=> ($IsAlloc |f#0@@0| (Tclass._System.___hFunc1 |#$T0@@8| |#$R@@8|) $h@@7) ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7))))
 :qid |unknown.0:0|
 :skolemid |692|
 :pattern ( ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7))
)))
(assert (forall ((arg0@@126 T@U) (arg1@@57 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1 arg0@@126 arg1@@57)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1|
 :pattern ( (Tclass._System.___hTotalFunc1 arg0@@126 arg1@@57))
)))
(assert (forall ((|#$T0@@9| T@U) (|#$R@@9| T@U) ) (!  (=> (and (= (type |#$T0@@9|) TyType) (= (type |#$R@@9|) TyType)) (= (Tag (Tclass._System.___hTotalFunc1 |#$T0@@9| |#$R@@9|)) Tagclass._System.___hTotalFunc1))
 :qid |unknown.0:0|
 :skolemid |693|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@9| |#$R@@9|))
)))
(assert (forall ((arg0@@127 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_0 arg0@@127)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_0|
 :pattern ( (Tclass._System.___hTotalFunc1_0 arg0@@127))
)))
(assert (forall ((|#$T0@@10| T@U) (|#$R@@10| T@U) ) (!  (=> (and (= (type |#$T0@@10|) TyType) (= (type |#$R@@10|) TyType)) (= (Tclass._System.___hTotalFunc1_0 (Tclass._System.___hTotalFunc1 |#$T0@@10| |#$R@@10|)) |#$T0@@10|))
 :qid |unknown.0:0|
 :skolemid |694|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@10| |#$R@@10|))
)))
(assert (forall ((arg0@@128 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_1 arg0@@128)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_1|
 :pattern ( (Tclass._System.___hTotalFunc1_1 arg0@@128))
)))
(assert (forall ((|#$T0@@11| T@U) (|#$R@@11| T@U) ) (!  (=> (and (= (type |#$T0@@11|) TyType) (= (type |#$R@@11|) TyType)) (= (Tclass._System.___hTotalFunc1_1 (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@11|)) |#$R@@11|))
 :qid |unknown.0:0|
 :skolemid |695|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@11|))
)))
(assert (forall ((|#$T0@@12| T@U) (|#$R@@12| T@U) (bx@@44 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@12|) TyType) (= (type |#$R@@12|) TyType)) (= (type bx@@44) BoxType)) ($IsBox bx@@44 (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|))) (and (= ($Box ($Unbox HandleTypeType bx@@44)) bx@@44) ($Is ($Unbox HandleTypeType bx@@44) (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|))))
 :qid |unknown.0:0|
 :skolemid |696|
 :pattern ( ($IsBox bx@@44 (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|)))
)))
(assert (forall ((|#$T0@@13| T@U) (|#$R@@13| T@U) (|f#0@@1| T@U) ) (!  (=> (and (and (= (type |#$T0@@13|) TyType) (= (type |#$R@@13|) TyType)) (= (type |f#0@@1|) HandleTypeType)) (and (=> ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|)) (and ($Is |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@13|)) (forall ((|x0#0@@1| T@U) ) (!  (=> (and (= (type |x0#0@@1|) BoxType) ($IsBox |x0#0@@1| |#$T0@@13|)) (Requires1 |#$T0@@13| |#$R@@13| $OneHeap |f#0@@1| |x0#0@@1|))
 :qid |unknown.0:0|
 :skolemid |697|
 :no-pattern (type |x0#0@@1|)
 :no-pattern (U_2_int |x0#0@@1|)
 :no-pattern (U_2_bool |x0#0@@1|)
)))) (=> (and ($Is |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@13|)) (forall ((|x0#0@@2| T@U) ) (!  (=> (and (= (type |x0#0@@2|) BoxType) ($IsBox |x0#0@@2| |#$T0@@13|)) (Requires1 |#$T0@@13| |#$R@@13| $OneHeap |f#0@@1| |x0#0@@2|))
 :qid |unknown.0:0|
 :skolemid |697|
 :no-pattern (type |x0#0@@2|)
 :no-pattern (U_2_int |x0#0@@2|)
 :no-pattern (U_2_bool |x0#0@@2|)
))) ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|)))))
 :qid |unknown.0:0|
 :skolemid |698|
 :pattern ( ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|)))
)))
(assert (forall ((|#$T0@@14| T@U) (|#$R@@14| T@U) (|f#0@@2| T@U) ($h@@8 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@14|) TyType) (= (type |#$R@@14|) TyType)) (= (type |f#0@@2|) HandleTypeType)) (= (type $h@@8) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8) ($IsAlloc |f#0@@2| (Tclass._System.___hPartialFunc1 |#$T0@@14| |#$R@@14|) $h@@8)) (=> ($IsAlloc |f#0@@2| (Tclass._System.___hPartialFunc1 |#$T0@@14| |#$R@@14|) $h@@8) ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8))))
 :qid |unknown.0:0|
 :skolemid |699|
 :pattern ( ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8))
)))
(assert (forall ((arg0@@129 T@U) ) (! (= (type (Tclass._System.___hFunc0 arg0@@129)) TyType)
 :qid |funType:Tclass._System.___hFunc0|
 :pattern ( (Tclass._System.___hFunc0 arg0@@129))
)))
(assert (forall ((|#$R@@15| T@U) ) (!  (=> (= (type |#$R@@15|) TyType) (= (Tag (Tclass._System.___hFunc0 |#$R@@15|)) Tagclass._System.___hFunc0))
 :qid |unknown.0:0|
 :skolemid |700|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@15|))
)))
(assert (forall ((arg0@@130 T@U) ) (! (= (type (Tclass._System.___hFunc0_0 arg0@@130)) TyType)
 :qid |funType:Tclass._System.___hFunc0_0|
 :pattern ( (Tclass._System.___hFunc0_0 arg0@@130))
)))
(assert (forall ((|#$R@@16| T@U) ) (!  (=> (= (type |#$R@@16|) TyType) (= (Tclass._System.___hFunc0_0 (Tclass._System.___hFunc0 |#$R@@16|)) |#$R@@16|))
 :qid |unknown.0:0|
 :skolemid |701|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@16|))
)))
(assert (forall ((|#$R@@17| T@U) (bx@@45 T@U) ) (!  (=> (and (and (= (type |#$R@@17|) TyType) (= (type bx@@45) BoxType)) ($IsBox bx@@45 (Tclass._System.___hFunc0 |#$R@@17|))) (and (= ($Box ($Unbox HandleTypeType bx@@45)) bx@@45) ($Is ($Unbox HandleTypeType bx@@45) (Tclass._System.___hFunc0 |#$R@@17|))))
 :qid |unknown.0:0|
 :skolemid |702|
 :pattern ( ($IsBox bx@@45 (Tclass._System.___hFunc0 |#$R@@17|)))
)))
(assert  (and (forall ((arg0@@131 T@U) (arg1@@58 T@U) (arg2@@16 T@U) ) (! (= (type (Apply0 arg0@@131 arg1@@58 arg2@@16)) BoxType)
 :qid |funType:Apply0|
 :pattern ( (Apply0 arg0@@131 arg1@@58 arg2@@16))
)) (forall ((arg0@@132 T@U) (arg1@@59 T@U) (arg2@@17 T@U) ) (! (= (type (Handle0 arg0@@132 arg1@@59 arg2@@17)) HandleTypeType)
 :qid |funType:Handle0|
 :pattern ( (Handle0 arg0@@132 arg1@@59 arg2@@17))
))))
(assert (forall ((t0@@27 T@U) (heap@@6 T@U) (h@@27 T@U) (r@@11 T@U) (rd@@2 T@U) ) (!  (=> (and (and (and (and (= (type t0@@27) TyType) (= (type heap@@6) (MapType0Type refType MapType1Type))) (= (type h@@27) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@11) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@2) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (= (Apply0 t0@@27 heap@@6 (Handle0 h@@27 r@@11 rd@@2)) (MapType0Select h@@27 heap@@6)))
 :qid |unknown.0:0|
 :skolemid |703|
 :pattern ( (Apply0 t0@@27 heap@@6 (Handle0 h@@27 r@@11 rd@@2)))
)))
(assert (forall ((t0@@28 T@U) (heap@@7 T@U) (h@@28 T@U) (r@@12 T@U) (rd@@3 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@28) TyType) (= (type heap@@7) (MapType0Type refType MapType1Type))) (= (type h@@28) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@12) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@3) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (U_2_bool (MapType0Select r@@12 heap@@7))) (Requires0 t0@@28 heap@@7 (Handle0 h@@28 r@@12 rd@@3)))
 :qid |unknown.0:0|
 :skolemid |704|
 :pattern ( (Requires0 t0@@28 heap@@7 (Handle0 h@@28 r@@12 rd@@3)))
)))
(assert (forall ((arg0@@133 T@U) (arg1@@60 T@U) (arg2@@18 T@U) ) (! (= (type (Reads0 arg0@@133 arg1@@60 arg2@@18)) (MapType0Type BoxType boolType))
 :qid |funType:Reads0|
 :pattern ( (Reads0 arg0@@133 arg1@@60 arg2@@18))
)))
(assert (forall ((t0@@29 T@U) (heap@@8 T@U) (h@@29 T@U) (r@@13 T@U) (rd@@4 T@U) (bx@@46 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@29) TyType) (= (type heap@@8) (MapType0Type refType MapType1Type))) (= (type h@@29) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@13) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@4) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (= (type bx@@46) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads0 t0@@29 heap@@8 (Handle0 h@@29 r@@13 rd@@4)) bx@@46)) (U_2_bool (MapType0Select (MapType0Select rd@@4 heap@@8) bx@@46))) (=> (U_2_bool (MapType0Select (MapType0Select rd@@4 heap@@8) bx@@46)) (U_2_bool (MapType0Select (Reads0 t0@@29 heap@@8 (Handle0 h@@29 r@@13 rd@@4)) bx@@46)))))
 :qid |unknown.0:0|
 :skolemid |705|
 :pattern ( (MapType0Select (Reads0 t0@@29 heap@@8 (Handle0 h@@29 r@@13 rd@@4)) bx@@46))
)))
(assert (forall ((t0@@30 T@U) (h0@@6 T@U) (h1@@6 T@U) (f@@17 T@U) ) (!  (=> (and (and (and (and (= (type t0@@30) TyType) (= (type h0@@6) (MapType0Type refType MapType1Type))) (= (type h1@@6) (MapType0Type refType MapType1Type))) (= (type f@@17) HandleTypeType)) (and (and (and ($HeapSucc h0@@6 h1@@6) (and ($IsGoodHeap h0@@6) ($IsGoodHeap h1@@6))) ($Is f@@17 (Tclass._System.___hFunc0 t0@@30))) (forall ((o@@60 T@U) (fld@@5 T@U) ) (! (let ((a@@85 (FieldTypeInv0 (type fld@@5))))
 (=> (and (and (= (type o@@60) refType) (= (type fld@@5) (FieldType a@@85))) (and (not (= o@@60 null)) (U_2_bool (MapType0Select (Reads0 t0@@30 h0@@6 f@@17) ($Box o@@60))))) (= (MapType1Select (MapType0Select h0@@6 o@@60) fld@@5) (MapType1Select (MapType0Select h1@@6 o@@60) fld@@5))))
 :qid |unknown.0:0|
 :skolemid |706|
 :no-pattern (type o@@60)
 :no-pattern (type fld@@5)
 :no-pattern (U_2_int o@@60)
 :no-pattern (U_2_bool o@@60)
 :no-pattern (U_2_int fld@@5)
 :no-pattern (U_2_bool fld@@5)
)))) (= (Reads0 t0@@30 h0@@6 f@@17) (Reads0 t0@@30 h1@@6 f@@17)))
 :qid |unknown.0:0|
 :skolemid |707|
 :pattern ( ($HeapSucc h0@@6 h1@@6) (Reads0 t0@@30 h1@@6 f@@17))
)))
(assert (forall ((t0@@31 T@U) (h0@@7 T@U) (h1@@7 T@U) (f@@18 T@U) ) (!  (=> (and (and (and (and (= (type t0@@31) TyType) (= (type h0@@7) (MapType0Type refType MapType1Type))) (= (type h1@@7) (MapType0Type refType MapType1Type))) (= (type f@@18) HandleTypeType)) (and (and (and ($HeapSucc h0@@7 h1@@7) (and ($IsGoodHeap h0@@7) ($IsGoodHeap h1@@7))) ($Is f@@18 (Tclass._System.___hFunc0 t0@@31))) (forall ((o@@61 T@U) (fld@@6 T@U) ) (! (let ((a@@86 (FieldTypeInv0 (type fld@@6))))
 (=> (and (and (= (type o@@61) refType) (= (type fld@@6) (FieldType a@@86))) (and (not (= o@@61 null)) (U_2_bool (MapType0Select (Reads0 t0@@31 h1@@7 f@@18) ($Box o@@61))))) (= (MapType1Select (MapType0Select h0@@7 o@@61) fld@@6) (MapType1Select (MapType0Select h1@@7 o@@61) fld@@6))))
 :qid |unknown.0:0|
 :skolemid |708|
 :no-pattern (type o@@61)
 :no-pattern (type fld@@6)
 :no-pattern (U_2_int o@@61)
 :no-pattern (U_2_bool o@@61)
 :no-pattern (U_2_int fld@@6)
 :no-pattern (U_2_bool fld@@6)
)))) (= (Reads0 t0@@31 h0@@7 f@@18) (Reads0 t0@@31 h1@@7 f@@18)))
 :qid |unknown.0:0|
 :skolemid |709|
 :pattern ( ($HeapSucc h0@@7 h1@@7) (Reads0 t0@@31 h1@@7 f@@18))
)))
(assert (forall ((t0@@32 T@U) (h0@@8 T@U) (h1@@8 T@U) (f@@19 T@U) ) (!  (=> (and (and (and (and (= (type t0@@32) TyType) (= (type h0@@8) (MapType0Type refType MapType1Type))) (= (type h1@@8) (MapType0Type refType MapType1Type))) (= (type f@@19) HandleTypeType)) (and (and (and ($HeapSucc h0@@8 h1@@8) (and ($IsGoodHeap h0@@8) ($IsGoodHeap h1@@8))) ($Is f@@19 (Tclass._System.___hFunc0 t0@@32))) (forall ((o@@62 T@U) (fld@@7 T@U) ) (! (let ((a@@87 (FieldTypeInv0 (type fld@@7))))
 (=> (and (and (= (type o@@62) refType) (= (type fld@@7) (FieldType a@@87))) (and (not (= o@@62 null)) (U_2_bool (MapType0Select (Reads0 t0@@32 h0@@8 f@@19) ($Box o@@62))))) (= (MapType1Select (MapType0Select h0@@8 o@@62) fld@@7) (MapType1Select (MapType0Select h1@@8 o@@62) fld@@7))))
 :qid |unknown.0:0|
 :skolemid |710|
 :no-pattern (type o@@62)
 :no-pattern (type fld@@7)
 :no-pattern (U_2_int o@@62)
 :no-pattern (U_2_bool o@@62)
 :no-pattern (U_2_int fld@@7)
 :no-pattern (U_2_bool fld@@7)
)))) (and (=> (Requires0 t0@@32 h0@@8 f@@19) (Requires0 t0@@32 h1@@8 f@@19)) (=> (Requires0 t0@@32 h1@@8 f@@19) (Requires0 t0@@32 h0@@8 f@@19))))
 :qid |unknown.0:0|
 :skolemid |711|
 :pattern ( ($HeapSucc h0@@8 h1@@8) (Requires0 t0@@32 h1@@8 f@@19))
)))
(assert (forall ((t0@@33 T@U) (h0@@9 T@U) (h1@@9 T@U) (f@@20 T@U) ) (!  (=> (and (and (and (and (= (type t0@@33) TyType) (= (type h0@@9) (MapType0Type refType MapType1Type))) (= (type h1@@9) (MapType0Type refType MapType1Type))) (= (type f@@20) HandleTypeType)) (and (and (and ($HeapSucc h0@@9 h1@@9) (and ($IsGoodHeap h0@@9) ($IsGoodHeap h1@@9))) ($Is f@@20 (Tclass._System.___hFunc0 t0@@33))) (forall ((o@@63 T@U) (fld@@8 T@U) ) (! (let ((a@@88 (FieldTypeInv0 (type fld@@8))))
 (=> (and (and (= (type o@@63) refType) (= (type fld@@8) (FieldType a@@88))) (and (not (= o@@63 null)) (U_2_bool (MapType0Select (Reads0 t0@@33 h1@@9 f@@20) ($Box o@@63))))) (= (MapType1Select (MapType0Select h0@@9 o@@63) fld@@8) (MapType1Select (MapType0Select h1@@9 o@@63) fld@@8))))
 :qid |unknown.0:0|
 :skolemid |712|
 :no-pattern (type o@@63)
 :no-pattern (type fld@@8)
 :no-pattern (U_2_int o@@63)
 :no-pattern (U_2_bool o@@63)
 :no-pattern (U_2_int fld@@8)
 :no-pattern (U_2_bool fld@@8)
)))) (and (=> (Requires0 t0@@33 h0@@9 f@@20) (Requires0 t0@@33 h1@@9 f@@20)) (=> (Requires0 t0@@33 h1@@9 f@@20) (Requires0 t0@@33 h0@@9 f@@20))))
 :qid |unknown.0:0|
 :skolemid |713|
 :pattern ( ($HeapSucc h0@@9 h1@@9) (Requires0 t0@@33 h1@@9 f@@20))
)))
(assert (forall ((t0@@34 T@U) (h0@@10 T@U) (h1@@10 T@U) (f@@21 T@U) ) (!  (=> (and (and (and (and (= (type t0@@34) TyType) (= (type h0@@10) (MapType0Type refType MapType1Type))) (= (type h1@@10) (MapType0Type refType MapType1Type))) (= (type f@@21) HandleTypeType)) (and (and (and ($HeapSucc h0@@10 h1@@10) (and ($IsGoodHeap h0@@10) ($IsGoodHeap h1@@10))) ($Is f@@21 (Tclass._System.___hFunc0 t0@@34))) (forall ((o@@64 T@U) (fld@@9 T@U) ) (! (let ((a@@89 (FieldTypeInv0 (type fld@@9))))
 (=> (and (and (= (type o@@64) refType) (= (type fld@@9) (FieldType a@@89))) (and (not (= o@@64 null)) (U_2_bool (MapType0Select (Reads0 t0@@34 h0@@10 f@@21) ($Box o@@64))))) (= (MapType1Select (MapType0Select h0@@10 o@@64) fld@@9) (MapType1Select (MapType0Select h1@@10 o@@64) fld@@9))))
 :qid |unknown.0:0|
 :skolemid |714|
 :no-pattern (type o@@64)
 :no-pattern (type fld@@9)
 :no-pattern (U_2_int o@@64)
 :no-pattern (U_2_bool o@@64)
 :no-pattern (U_2_int fld@@9)
 :no-pattern (U_2_bool fld@@9)
)))) (= (Apply0 t0@@34 h0@@10 f@@21) (Apply0 t0@@34 h1@@10 f@@21)))
 :qid |unknown.0:0|
 :skolemid |715|
 :pattern ( ($HeapSucc h0@@10 h1@@10) (Apply0 t0@@34 h1@@10 f@@21))
)))
(assert (forall ((t0@@35 T@U) (h0@@11 T@U) (h1@@11 T@U) (f@@22 T@U) ) (!  (=> (and (and (and (and (= (type t0@@35) TyType) (= (type h0@@11) (MapType0Type refType MapType1Type))) (= (type h1@@11) (MapType0Type refType MapType1Type))) (= (type f@@22) HandleTypeType)) (and (and (and ($HeapSucc h0@@11 h1@@11) (and ($IsGoodHeap h0@@11) ($IsGoodHeap h1@@11))) ($Is f@@22 (Tclass._System.___hFunc0 t0@@35))) (forall ((o@@65 T@U) (fld@@10 T@U) ) (! (let ((a@@90 (FieldTypeInv0 (type fld@@10))))
 (=> (and (and (= (type o@@65) refType) (= (type fld@@10) (FieldType a@@90))) (and (not (= o@@65 null)) (U_2_bool (MapType0Select (Reads0 t0@@35 h1@@11 f@@22) ($Box o@@65))))) (= (MapType1Select (MapType0Select h0@@11 o@@65) fld@@10) (MapType1Select (MapType0Select h1@@11 o@@65) fld@@10))))
 :qid |unknown.0:0|
 :skolemid |716|
 :no-pattern (type o@@65)
 :no-pattern (type fld@@10)
 :no-pattern (U_2_int o@@65)
 :no-pattern (U_2_bool o@@65)
 :no-pattern (U_2_int fld@@10)
 :no-pattern (U_2_bool fld@@10)
)))) (= (Apply0 t0@@35 h0@@11 f@@22) (Apply0 t0@@35 h1@@11 f@@22)))
 :qid |unknown.0:0|
 :skolemid |717|
 :pattern ( ($HeapSucc h0@@11 h1@@11) (Apply0 t0@@35 h1@@11 f@@22))
)))
(assert (forall ((t0@@36 T@U) (heap@@9 T@U) (f@@23 T@U) ) (!  (=> (and (and (and (= (type t0@@36) TyType) (= (type heap@@9) (MapType0Type refType MapType1Type))) (= (type f@@23) HandleTypeType)) (and ($IsGoodHeap heap@@9) ($Is f@@23 (Tclass._System.___hFunc0 t0@@36)))) (and (=> (|Set#Equal| (Reads0 t0@@36 $OneHeap f@@23) (|Set#Empty| BoxType)) (|Set#Equal| (Reads0 t0@@36 heap@@9 f@@23) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads0 t0@@36 heap@@9 f@@23) (|Set#Empty| BoxType)) (|Set#Equal| (Reads0 t0@@36 $OneHeap f@@23) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |718|
 :pattern ( (Reads0 t0@@36 $OneHeap f@@23) ($IsGoodHeap heap@@9))
 :pattern ( (Reads0 t0@@36 heap@@9 f@@23))
)))
(assert (forall ((t0@@37 T@U) (heap@@10 T@U) (f@@24 T@U) ) (!  (=> (and (and (and (= (type t0@@37) TyType) (= (type heap@@10) (MapType0Type refType MapType1Type))) (= (type f@@24) HandleTypeType)) (and (and ($IsGoodHeap heap@@10) ($Is f@@24 (Tclass._System.___hFunc0 t0@@37))) (|Set#Equal| (Reads0 t0@@37 $OneHeap f@@24) (|Set#Empty| BoxType)))) (and (=> (Requires0 t0@@37 $OneHeap f@@24) (Requires0 t0@@37 heap@@10 f@@24)) (=> (Requires0 t0@@37 heap@@10 f@@24) (Requires0 t0@@37 $OneHeap f@@24))))
 :qid |unknown.0:0|
 :skolemid |719|
 :pattern ( (Requires0 t0@@37 $OneHeap f@@24) ($IsGoodHeap heap@@10))
 :pattern ( (Requires0 t0@@37 heap@@10 f@@24))
)))
(assert (forall ((f@@25 T@U) (t0@@38 T@U) ) (!  (=> (and (= (type f@@25) HandleTypeType) (= (type t0@@38) TyType)) (and (=> ($Is f@@25 (Tclass._System.___hFunc0 t0@@38)) (forall ((h@@30 T@U) ) (!  (=> (= (type h@@30) (MapType0Type refType MapType1Type)) (=> (and ($IsGoodHeap h@@30) (Requires0 t0@@38 h@@30 f@@25)) ($IsBox (Apply0 t0@@38 h@@30 f@@25) t0@@38)))
 :qid |DafnyPre.515:12|
 :skolemid |720|
 :pattern ( (Apply0 t0@@38 h@@30 f@@25))
))) (=> (forall ((h@@31 T@U) ) (!  (=> (= (type h@@31) (MapType0Type refType MapType1Type)) (=> (and ($IsGoodHeap h@@31) (Requires0 t0@@38 h@@31 f@@25)) ($IsBox (Apply0 t0@@38 h@@31 f@@25) t0@@38)))
 :qid |DafnyPre.515:12|
 :skolemid |720|
 :pattern ( (Apply0 t0@@38 h@@31 f@@25))
)) ($Is f@@25 (Tclass._System.___hFunc0 t0@@38)))))
 :qid |unknown.0:0|
 :skolemid |721|
 :pattern ( ($Is f@@25 (Tclass._System.___hFunc0 t0@@38)))
)))
(assert (forall ((f@@26 T@U) (t0@@39 T@U) (u0@@0 T@U) ) (!  (=> (and (and (and (= (type f@@26) HandleTypeType) (= (type t0@@39) TyType)) (= (type u0@@0) TyType)) (and ($Is f@@26 (Tclass._System.___hFunc0 t0@@39)) (forall ((bx@@47 T@U) ) (!  (=> (and (= (type bx@@47) BoxType) ($IsBox bx@@47 t0@@39)) ($IsBox bx@@47 u0@@0))
 :qid |unknown.0:0|
 :skolemid |722|
 :pattern ( ($IsBox bx@@47 t0@@39))
 :pattern ( ($IsBox bx@@47 u0@@0))
)))) ($Is f@@26 (Tclass._System.___hFunc0 u0@@0)))
 :qid |unknown.0:0|
 :skolemid |723|
 :pattern ( ($Is f@@26 (Tclass._System.___hFunc0 t0@@39)) ($Is f@@26 (Tclass._System.___hFunc0 u0@@0)))
)))
(assert (forall ((f@@27 T@U) (t0@@40 T@U) (h@@32 T@U) ) (!  (=> (and (and (and (= (type f@@27) HandleTypeType) (= (type t0@@40) TyType)) (= (type h@@32) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@32)) (and (=> ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@40) h@@32) (=> (Requires0 t0@@40 h@@32 f@@27) (forall ((r@@14 T@U) ) (!  (=> (= (type r@@14) refType) (=> (and (not (= r@@14 null)) (U_2_bool (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@14)))) (U_2_bool (MapType1Select (MapType0Select h@@32 r@@14) alloc))))
 :qid |unknown.0:0|
 :skolemid |724|
 :pattern ( (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@14)))
)))) (=> (=> (Requires0 t0@@40 h@@32 f@@27) (forall ((r@@15 T@U) ) (!  (=> (= (type r@@15) refType) (=> (and (not (= r@@15 null)) (U_2_bool (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@15)))) (U_2_bool (MapType1Select (MapType0Select h@@32 r@@15) alloc))))
 :qid |unknown.0:0|
 :skolemid |724|
 :pattern ( (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@15)))
))) ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@40) h@@32))))
 :qid |unknown.0:0|
 :skolemid |725|
 :pattern ( ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@40) h@@32))
)))
(assert (forall ((f@@28 T@U) (t0@@41 T@U) (h@@33 T@U) ) (!  (=> (and (and (and (and (= (type f@@28) HandleTypeType) (= (type t0@@41) TyType)) (= (type h@@33) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@33) ($IsAlloc f@@28 (Tclass._System.___hFunc0 t0@@41) h@@33))) (Requires0 t0@@41 h@@33 f@@28)) ($IsAllocBox (Apply0 t0@@41 h@@33 f@@28) t0@@41 h@@33))
 :qid |unknown.0:0|
 :skolemid |726|
 :pattern ( ($IsAlloc f@@28 (Tclass._System.___hFunc0 t0@@41) h@@33))
)))
(assert (forall ((arg0@@134 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0 arg0@@134)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0|
 :pattern ( (Tclass._System.___hPartialFunc0 arg0@@134))
)))
(assert (forall ((|#$R@@18| T@U) ) (!  (=> (= (type |#$R@@18|) TyType) (= (Tag (Tclass._System.___hPartialFunc0 |#$R@@18|)) Tagclass._System.___hPartialFunc0))
 :qid |unknown.0:0|
 :skolemid |727|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@18|))
)))
(assert (forall ((arg0@@135 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0_0 arg0@@135)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0_0|
 :pattern ( (Tclass._System.___hPartialFunc0_0 arg0@@135))
)))
(assert (forall ((|#$R@@19| T@U) ) (!  (=> (= (type |#$R@@19|) TyType) (= (Tclass._System.___hPartialFunc0_0 (Tclass._System.___hPartialFunc0 |#$R@@19|)) |#$R@@19|))
 :qid |unknown.0:0|
 :skolemid |728|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@19|))
)))
(assert (forall ((|#$R@@20| T@U) (bx@@48 T@U) ) (!  (=> (and (and (= (type |#$R@@20|) TyType) (= (type bx@@48) BoxType)) ($IsBox bx@@48 (Tclass._System.___hPartialFunc0 |#$R@@20|))) (and (= ($Box ($Unbox HandleTypeType bx@@48)) bx@@48) ($Is ($Unbox HandleTypeType bx@@48) (Tclass._System.___hPartialFunc0 |#$R@@20|))))
 :qid |unknown.0:0|
 :skolemid |729|
 :pattern ( ($IsBox bx@@48 (Tclass._System.___hPartialFunc0 |#$R@@20|)))
)))
(assert (forall ((|#$R@@21| T@U) (|f#0@@3| T@U) ) (!  (=> (and (= (type |#$R@@21|) TyType) (= (type |f#0@@3|) HandleTypeType)) (and (=> ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|)) (and ($Is |f#0@@3| (Tclass._System.___hFunc0 |#$R@@21|)) (|Set#Equal| (Reads0 |#$R@@21| $OneHeap |f#0@@3|) (|Set#Empty| BoxType)))) (=> (and ($Is |f#0@@3| (Tclass._System.___hFunc0 |#$R@@21|)) (|Set#Equal| (Reads0 |#$R@@21| $OneHeap |f#0@@3|) (|Set#Empty| BoxType))) ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|)))))
 :qid |unknown.0:0|
 :skolemid |730|
 :pattern ( ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|)))
)))
(assert (forall ((|#$R@@22| T@U) (|f#0@@4| T@U) ($h@@9 T@U) ) (!  (=> (and (and (= (type |#$R@@22|) TyType) (= (type |f#0@@4|) HandleTypeType)) (= (type $h@@9) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9) ($IsAlloc |f#0@@4| (Tclass._System.___hFunc0 |#$R@@22|) $h@@9)) (=> ($IsAlloc |f#0@@4| (Tclass._System.___hFunc0 |#$R@@22|) $h@@9) ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9))))
 :qid |unknown.0:0|
 :skolemid |731|
 :pattern ( ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9))
)))
(assert (forall ((arg0@@136 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0 arg0@@136)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0|
 :pattern ( (Tclass._System.___hTotalFunc0 arg0@@136))
)))
(assert (forall ((|#$R@@23| T@U) ) (!  (=> (= (type |#$R@@23|) TyType) (= (Tag (Tclass._System.___hTotalFunc0 |#$R@@23|)) Tagclass._System.___hTotalFunc0))
 :qid |unknown.0:0|
 :skolemid |732|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@23|))
)))
(assert (forall ((arg0@@137 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0_0 arg0@@137)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0_0|
 :pattern ( (Tclass._System.___hTotalFunc0_0 arg0@@137))
)))
(assert (forall ((|#$R@@24| T@U) ) (!  (=> (= (type |#$R@@24|) TyType) (= (Tclass._System.___hTotalFunc0_0 (Tclass._System.___hTotalFunc0 |#$R@@24|)) |#$R@@24|))
 :qid |unknown.0:0|
 :skolemid |733|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@24|))
)))
(assert (forall ((|#$R@@25| T@U) (bx@@49 T@U) ) (!  (=> (and (and (= (type |#$R@@25|) TyType) (= (type bx@@49) BoxType)) ($IsBox bx@@49 (Tclass._System.___hTotalFunc0 |#$R@@25|))) (and (= ($Box ($Unbox HandleTypeType bx@@49)) bx@@49) ($Is ($Unbox HandleTypeType bx@@49) (Tclass._System.___hTotalFunc0 |#$R@@25|))))
 :qid |unknown.0:0|
 :skolemid |734|
 :pattern ( ($IsBox bx@@49 (Tclass._System.___hTotalFunc0 |#$R@@25|)))
)))
(assert (forall ((|#$R@@26| T@U) (|f#0@@5| T@U) ) (!  (=> (and (= (type |#$R@@26|) TyType) (= (type |f#0@@5|) HandleTypeType)) (and (=> ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|)) (and ($Is |f#0@@5| (Tclass._System.___hPartialFunc0 |#$R@@26|)) (Requires0 |#$R@@26| $OneHeap |f#0@@5|))) (=> (and ($Is |f#0@@5| (Tclass._System.___hPartialFunc0 |#$R@@26|)) (Requires0 |#$R@@26| $OneHeap |f#0@@5|)) ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|)))))
 :qid |unknown.0:0|
 :skolemid |735|
 :pattern ( ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|)))
)))
(assert (forall ((|#$R@@27| T@U) (|f#0@@6| T@U) ($h@@10 T@U) ) (!  (=> (and (and (= (type |#$R@@27|) TyType) (= (type |f#0@@6|) HandleTypeType)) (= (type $h@@10) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10) ($IsAlloc |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|) $h@@10)) (=> ($IsAlloc |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|) $h@@10) ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10))))
 :qid |unknown.0:0|
 :skolemid |736|
 :pattern ( ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10))
)))
(assert (forall ((arg0@@138 T@U) (arg1@@61 T@U) (arg2@@19 T@U) ) (! (= (type (Tclass._System.___hFunc2 arg0@@138 arg1@@61 arg2@@19)) TyType)
 :qid |funType:Tclass._System.___hFunc2|
 :pattern ( (Tclass._System.___hFunc2 arg0@@138 arg1@@61 arg2@@19))
)))
(assert (forall ((|#$T0@@15| T@U) (|#$T1| T@U) (|#$R@@28| T@U) ) (!  (=> (and (and (= (type |#$T0@@15|) TyType) (= (type |#$T1|) TyType)) (= (type |#$R@@28|) TyType)) (= (Tag (Tclass._System.___hFunc2 |#$T0@@15| |#$T1| |#$R@@28|)) Tagclass._System.___hFunc2))
 :qid |unknown.0:0|
 :skolemid |737|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@15| |#$T1| |#$R@@28|))
)))
(assert (forall ((arg0@@139 T@U) ) (! (= (type (Tclass._System.___hFunc2_0 arg0@@139)) TyType)
 :qid |funType:Tclass._System.___hFunc2_0|
 :pattern ( (Tclass._System.___hFunc2_0 arg0@@139))
)))
(assert (forall ((|#$T0@@16| T@U) (|#$T1@@0| T@U) (|#$R@@29| T@U) ) (!  (=> (and (and (= (type |#$T0@@16|) TyType) (= (type |#$T1@@0|) TyType)) (= (type |#$R@@29|) TyType)) (= (Tclass._System.___hFunc2_0 (Tclass._System.___hFunc2 |#$T0@@16| |#$T1@@0| |#$R@@29|)) |#$T0@@16|))
 :qid |unknown.0:0|
 :skolemid |738|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@16| |#$T1@@0| |#$R@@29|))
)))
(assert (forall ((arg0@@140 T@U) ) (! (= (type (Tclass._System.___hFunc2_1 arg0@@140)) TyType)
 :qid |funType:Tclass._System.___hFunc2_1|
 :pattern ( (Tclass._System.___hFunc2_1 arg0@@140))
)))
(assert (forall ((|#$T0@@17| T@U) (|#$T1@@1| T@U) (|#$R@@30| T@U) ) (!  (=> (and (and (= (type |#$T0@@17|) TyType) (= (type |#$T1@@1|) TyType)) (= (type |#$R@@30|) TyType)) (= (Tclass._System.___hFunc2_1 (Tclass._System.___hFunc2 |#$T0@@17| |#$T1@@1| |#$R@@30|)) |#$T1@@1|))
 :qid |unknown.0:0|
 :skolemid |739|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@17| |#$T1@@1| |#$R@@30|))
)))
(assert (forall ((arg0@@141 T@U) ) (! (= (type (Tclass._System.___hFunc2_2 arg0@@141)) TyType)
 :qid |funType:Tclass._System.___hFunc2_2|
 :pattern ( (Tclass._System.___hFunc2_2 arg0@@141))
)))
(assert (forall ((|#$T0@@18| T@U) (|#$T1@@2| T@U) (|#$R@@31| T@U) ) (!  (=> (and (and (= (type |#$T0@@18|) TyType) (= (type |#$T1@@2|) TyType)) (= (type |#$R@@31|) TyType)) (= (Tclass._System.___hFunc2_2 (Tclass._System.___hFunc2 |#$T0@@18| |#$T1@@2| |#$R@@31|)) |#$R@@31|))
 :qid |unknown.0:0|
 :skolemid |740|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@18| |#$T1@@2| |#$R@@31|))
)))
(assert (forall ((|#$T0@@19| T@U) (|#$T1@@3| T@U) (|#$R@@32| T@U) (bx@@50 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@19|) TyType) (= (type |#$T1@@3|) TyType)) (= (type |#$R@@32|) TyType)) (= (type bx@@50) BoxType)) ($IsBox bx@@50 (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|))) (and (= ($Box ($Unbox HandleTypeType bx@@50)) bx@@50) ($Is ($Unbox HandleTypeType bx@@50) (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|))))
 :qid |unknown.0:0|
 :skolemid |741|
 :pattern ( ($IsBox bx@@50 (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|)))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (forall ((arg0@@142 T@T) (arg1@@62 T@T) (arg2@@20 T@T) (arg3@@3 T@T) ) (! (= (Ctor (MapType3Type arg0@@142 arg1@@62 arg2@@20 arg3@@3)) 24)
 :qid |ctor:MapType3Type|
)) (forall ((arg0@@143 T@T) (arg1@@63 T@T) (arg2@@21 T@T) (arg3@@4 T@T) ) (! (= (MapType3TypeInv0 (MapType3Type arg0@@143 arg1@@63 arg2@@21 arg3@@4)) arg0@@143)
 :qid |typeInv:MapType3TypeInv0|
 :pattern ( (MapType3Type arg0@@143 arg1@@63 arg2@@21 arg3@@4))
))) (forall ((arg0@@144 T@T) (arg1@@64 T@T) (arg2@@22 T@T) (arg3@@5 T@T) ) (! (= (MapType3TypeInv1 (MapType3Type arg0@@144 arg1@@64 arg2@@22 arg3@@5)) arg1@@64)
 :qid |typeInv:MapType3TypeInv1|
 :pattern ( (MapType3Type arg0@@144 arg1@@64 arg2@@22 arg3@@5))
))) (forall ((arg0@@145 T@T) (arg1@@65 T@T) (arg2@@23 T@T) (arg3@@6 T@T) ) (! (= (MapType3TypeInv2 (MapType3Type arg0@@145 arg1@@65 arg2@@23 arg3@@6)) arg2@@23)
 :qid |typeInv:MapType3TypeInv2|
 :pattern ( (MapType3Type arg0@@145 arg1@@65 arg2@@23 arg3@@6))
))) (forall ((arg0@@146 T@T) (arg1@@66 T@T) (arg2@@24 T@T) (arg3@@7 T@T) ) (! (= (MapType3TypeInv3 (MapType3Type arg0@@146 arg1@@66 arg2@@24 arg3@@7)) arg3@@7)
 :qid |typeInv:MapType3TypeInv3|
 :pattern ( (MapType3Type arg0@@146 arg1@@66 arg2@@24 arg3@@7))
))) (forall ((arg0@@147 T@U) (arg1@@67 T@U) (arg2@@25 T@U) (arg3@@8 T@U) ) (! (let ((aVar3 (MapType3TypeInv3 (type arg0@@147))))
(= (type (MapType3Select arg0@@147 arg1@@67 arg2@@25 arg3@@8)) aVar3))
 :qid |funType:MapType3Select|
 :pattern ( (MapType3Select arg0@@147 arg1@@67 arg2@@25 arg3@@8))
))) (forall ((arg0@@148 T@U) (arg1@@68 T@U) (arg2@@26 T@U) (arg3@@9 T@U) (arg4@@1 T@U) ) (! (let ((aVar3@@0 (type arg4@@1)))
(let ((aVar2@@2 (type arg3@@9)))
(let ((aVar1@@3 (type arg2@@26)))
(let ((aVar0@@1 (type arg1@@68)))
(= (type (MapType3Store arg0@@148 arg1@@68 arg2@@26 arg3@@9 arg4@@1)) (MapType3Type aVar0@@1 aVar1@@3 aVar2@@2 aVar3@@0))))))
 :qid |funType:MapType3Store|
 :pattern ( (MapType3Store arg0@@148 arg1@@68 arg2@@26 arg3@@9 arg4@@1))
))) (forall ((m@@31 T@U) (x0@@9 T@U) (x1@@3 T@U) (x2 T@U) (val@@10 T@U) ) (! (let ((aVar3@@1 (MapType3TypeInv3 (type m@@31))))
 (=> (= (type val@@10) aVar3@@1) (= (MapType3Select (MapType3Store m@@31 x0@@9 x1@@3 x2 val@@10) x0@@9 x1@@3 x2) val@@10)))
 :qid |mapAx0:MapType3Select|
 :weight 0
))) (and (and (and (forall ((val@@11 T@U) (m@@32 T@U) (x0@@10 T@U) (x1@@4 T@U) (x2@@0 T@U) (y0@@6 T@U) (y1@@2 T@U) (y2 T@U) ) (!  (or (= x0@@10 y0@@6) (= (MapType3Select (MapType3Store m@@32 x0@@10 x1@@4 x2@@0 val@@11) y0@@6 y1@@2 y2) (MapType3Select m@@32 y0@@6 y1@@2 y2)))
 :qid |mapAx1:MapType3Select:0|
 :weight 0
)) (forall ((val@@12 T@U) (m@@33 T@U) (x0@@11 T@U) (x1@@5 T@U) (x2@@1 T@U) (y0@@7 T@U) (y1@@3 T@U) (y2@@0 T@U) ) (!  (or (= x1@@5 y1@@3) (= (MapType3Select (MapType3Store m@@33 x0@@11 x1@@5 x2@@1 val@@12) y0@@7 y1@@3 y2@@0) (MapType3Select m@@33 y0@@7 y1@@3 y2@@0)))
 :qid |mapAx1:MapType3Select:1|
 :weight 0
))) (forall ((val@@13 T@U) (m@@34 T@U) (x0@@12 T@U) (x1@@6 T@U) (x2@@2 T@U) (y0@@8 T@U) (y1@@4 T@U) (y2@@1 T@U) ) (!  (or (= x2@@2 y2@@1) (= (MapType3Select (MapType3Store m@@34 x0@@12 x1@@6 x2@@2 val@@13) y0@@8 y1@@4 y2@@1) (MapType3Select m@@34 y0@@8 y1@@4 y2@@1)))
 :qid |mapAx1:MapType3Select:2|
 :weight 0
))) (forall ((val@@14 T@U) (m@@35 T@U) (x0@@13 T@U) (x1@@7 T@U) (x2@@3 T@U) (y0@@9 T@U) (y1@@5 T@U) (y2@@2 T@U) ) (!  (or true (= (MapType3Select (MapType3Store m@@35 x0@@13 x1@@7 x2@@3 val@@14) y0@@9 y1@@5 y2@@2) (MapType3Select m@@35 y0@@9 y1@@5 y2@@2)))
 :qid |mapAx2:MapType3Select|
 :weight 0
)))) (forall ((arg0@@149 T@U) (arg1@@69 T@U) (arg2@@27 T@U) (arg3@@10 T@U) (arg4@@2 T@U) (arg5 T@U) (arg6 T@U) ) (! (= (type (Apply2 arg0@@149 arg1@@69 arg2@@27 arg3@@10 arg4@@2 arg5 arg6)) BoxType)
 :qid |funType:Apply2|
 :pattern ( (Apply2 arg0@@149 arg1@@69 arg2@@27 arg3@@10 arg4@@2 arg5 arg6))
))) (forall ((arg0@@150 T@U) (arg1@@70 T@U) (arg2@@28 T@U) ) (! (= (type (Handle2 arg0@@150 arg1@@70 arg2@@28)) HandleTypeType)
 :qid |funType:Handle2|
 :pattern ( (Handle2 arg0@@150 arg1@@70 arg2@@28))
))))
(assert (forall ((t0@@42 T@U) (t1@@18 T@U) (t2 T@U) (heap@@11 T@U) (h@@34 T@U) (r@@16 T@U) (rd@@5 T@U) (bx0@@15 T@U) (bx1 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@42) TyType) (= (type t1@@18) TyType)) (= (type t2) TyType)) (= (type heap@@11) (MapType0Type refType MapType1Type))) (= (type h@@34) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@16) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@5) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@15) BoxType)) (= (type bx1) BoxType)) (= (Apply2 t0@@42 t1@@18 t2 heap@@11 (Handle2 h@@34 r@@16 rd@@5) bx0@@15 bx1) (MapType3Select h@@34 heap@@11 bx0@@15 bx1)))
 :qid |unknown.0:0|
 :skolemid |742|
 :pattern ( (Apply2 t0@@42 t1@@18 t2 heap@@11 (Handle2 h@@34 r@@16 rd@@5) bx0@@15 bx1))
)))
(assert (forall ((t0@@43 T@U) (t1@@19 T@U) (t2@@0 T@U) (heap@@12 T@U) (h@@35 T@U) (r@@17 T@U) (rd@@6 T@U) (bx0@@16 T@U) (bx1@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@43) TyType) (= (type t1@@19) TyType)) (= (type t2@@0) TyType)) (= (type heap@@12) (MapType0Type refType MapType1Type))) (= (type h@@35) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@17) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@6) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@16) BoxType)) (= (type bx1@@0) BoxType)) (U_2_bool (MapType3Select r@@17 heap@@12 bx0@@16 bx1@@0))) (Requires2 t0@@43 t1@@19 t2@@0 heap@@12 (Handle2 h@@35 r@@17 rd@@6) bx0@@16 bx1@@0))
 :qid |unknown.0:0|
 :skolemid |743|
 :pattern ( (Requires2 t0@@43 t1@@19 t2@@0 heap@@12 (Handle2 h@@35 r@@17 rd@@6) bx0@@16 bx1@@0))
)))
(assert (forall ((arg0@@151 T@U) (arg1@@71 T@U) (arg2@@29 T@U) (arg3@@11 T@U) (arg4@@3 T@U) (arg5@@0 T@U) (arg6@@0 T@U) ) (! (= (type (Reads2 arg0@@151 arg1@@71 arg2@@29 arg3@@11 arg4@@3 arg5@@0 arg6@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads2|
 :pattern ( (Reads2 arg0@@151 arg1@@71 arg2@@29 arg3@@11 arg4@@3 arg5@@0 arg6@@0))
)))
(assert (forall ((t0@@44 T@U) (t1@@20 T@U) (t2@@1 T@U) (heap@@13 T@U) (h@@36 T@U) (r@@18 T@U) (rd@@7 T@U) (bx0@@17 T@U) (bx1@@1 T@U) (bx@@51 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@44) TyType) (= (type t1@@20) TyType)) (= (type t2@@1) TyType)) (= (type heap@@13) (MapType0Type refType MapType1Type))) (= (type h@@36) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@18) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@7) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@17) BoxType)) (= (type bx1@@1) BoxType)) (= (type bx@@51) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads2 t0@@44 t1@@20 t2@@1 heap@@13 (Handle2 h@@36 r@@18 rd@@7) bx0@@17 bx1@@1) bx@@51)) (U_2_bool (MapType0Select (MapType3Select rd@@7 heap@@13 bx0@@17 bx1@@1) bx@@51))) (=> (U_2_bool (MapType0Select (MapType3Select rd@@7 heap@@13 bx0@@17 bx1@@1) bx@@51)) (U_2_bool (MapType0Select (Reads2 t0@@44 t1@@20 t2@@1 heap@@13 (Handle2 h@@36 r@@18 rd@@7) bx0@@17 bx1@@1) bx@@51)))))
 :qid |unknown.0:0|
 :skolemid |744|
 :pattern ( (MapType0Select (Reads2 t0@@44 t1@@20 t2@@1 heap@@13 (Handle2 h@@36 r@@18 rd@@7) bx0@@17 bx1@@1) bx@@51))
)))
(assert (forall ((t0@@45 T@U) (t1@@21 T@U) (t2@@2 T@U) (h0@@12 T@U) (h1@@12 T@U) (f@@29 T@U) (bx0@@18 T@U) (bx1@@2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@45) TyType) (= (type t1@@21) TyType)) (= (type t2@@2) TyType)) (= (type h0@@12) (MapType0Type refType MapType1Type))) (= (type h1@@12) (MapType0Type refType MapType1Type))) (= (type f@@29) HandleTypeType)) (= (type bx0@@18) BoxType)) (= (type bx1@@2) BoxType)) (and (and (and ($HeapSucc h0@@12 h1@@12) (and ($IsGoodHeap h0@@12) ($IsGoodHeap h1@@12))) (and (and ($IsBox bx0@@18 t0@@45) ($IsBox bx1@@2 t1@@21)) ($Is f@@29 (Tclass._System.___hFunc2 t0@@45 t1@@21 t2@@2)))) (forall ((o@@66 T@U) (fld@@11 T@U) ) (! (let ((a@@91 (FieldTypeInv0 (type fld@@11))))
 (=> (and (and (= (type o@@66) refType) (= (type fld@@11) (FieldType a@@91))) (and (not (= o@@66 null)) (U_2_bool (MapType0Select (Reads2 t0@@45 t1@@21 t2@@2 h0@@12 f@@29 bx0@@18 bx1@@2) ($Box o@@66))))) (= (MapType1Select (MapType0Select h0@@12 o@@66) fld@@11) (MapType1Select (MapType0Select h1@@12 o@@66) fld@@11))))
 :qid |unknown.0:0|
 :skolemid |745|
 :no-pattern (type o@@66)
 :no-pattern (type fld@@11)
 :no-pattern (U_2_int o@@66)
 :no-pattern (U_2_bool o@@66)
 :no-pattern (U_2_int fld@@11)
 :no-pattern (U_2_bool fld@@11)
)))) (= (Reads2 t0@@45 t1@@21 t2@@2 h0@@12 f@@29 bx0@@18 bx1@@2) (Reads2 t0@@45 t1@@21 t2@@2 h1@@12 f@@29 bx0@@18 bx1@@2)))
 :qid |unknown.0:0|
 :skolemid |746|
 :pattern ( ($HeapSucc h0@@12 h1@@12) (Reads2 t0@@45 t1@@21 t2@@2 h1@@12 f@@29 bx0@@18 bx1@@2))
)))
(assert (forall ((t0@@46 T@U) (t1@@22 T@U) (t2@@3 T@U) (h0@@13 T@U) (h1@@13 T@U) (f@@30 T@U) (bx0@@19 T@U) (bx1@@3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@46) TyType) (= (type t1@@22) TyType)) (= (type t2@@3) TyType)) (= (type h0@@13) (MapType0Type refType MapType1Type))) (= (type h1@@13) (MapType0Type refType MapType1Type))) (= (type f@@30) HandleTypeType)) (= (type bx0@@19) BoxType)) (= (type bx1@@3) BoxType)) (and (and (and ($HeapSucc h0@@13 h1@@13) (and ($IsGoodHeap h0@@13) ($IsGoodHeap h1@@13))) (and (and ($IsBox bx0@@19 t0@@46) ($IsBox bx1@@3 t1@@22)) ($Is f@@30 (Tclass._System.___hFunc2 t0@@46 t1@@22 t2@@3)))) (forall ((o@@67 T@U) (fld@@12 T@U) ) (! (let ((a@@92 (FieldTypeInv0 (type fld@@12))))
 (=> (and (and (= (type o@@67) refType) (= (type fld@@12) (FieldType a@@92))) (and (not (= o@@67 null)) (U_2_bool (MapType0Select (Reads2 t0@@46 t1@@22 t2@@3 h1@@13 f@@30 bx0@@19 bx1@@3) ($Box o@@67))))) (= (MapType1Select (MapType0Select h0@@13 o@@67) fld@@12) (MapType1Select (MapType0Select h1@@13 o@@67) fld@@12))))
 :qid |unknown.0:0|
 :skolemid |747|
 :no-pattern (type o@@67)
 :no-pattern (type fld@@12)
 :no-pattern (U_2_int o@@67)
 :no-pattern (U_2_bool o@@67)
 :no-pattern (U_2_int fld@@12)
 :no-pattern (U_2_bool fld@@12)
)))) (= (Reads2 t0@@46 t1@@22 t2@@3 h0@@13 f@@30 bx0@@19 bx1@@3) (Reads2 t0@@46 t1@@22 t2@@3 h1@@13 f@@30 bx0@@19 bx1@@3)))
 :qid |unknown.0:0|
 :skolemid |748|
 :pattern ( ($HeapSucc h0@@13 h1@@13) (Reads2 t0@@46 t1@@22 t2@@3 h1@@13 f@@30 bx0@@19 bx1@@3))
)))
(assert (forall ((t0@@47 T@U) (t1@@23 T@U) (t2@@4 T@U) (h0@@14 T@U) (h1@@14 T@U) (f@@31 T@U) (bx0@@20 T@U) (bx1@@4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@47) TyType) (= (type t1@@23) TyType)) (= (type t2@@4) TyType)) (= (type h0@@14) (MapType0Type refType MapType1Type))) (= (type h1@@14) (MapType0Type refType MapType1Type))) (= (type f@@31) HandleTypeType)) (= (type bx0@@20) BoxType)) (= (type bx1@@4) BoxType)) (and (and (and ($HeapSucc h0@@14 h1@@14) (and ($IsGoodHeap h0@@14) ($IsGoodHeap h1@@14))) (and (and ($IsBox bx0@@20 t0@@47) ($IsBox bx1@@4 t1@@23)) ($Is f@@31 (Tclass._System.___hFunc2 t0@@47 t1@@23 t2@@4)))) (forall ((o@@68 T@U) (fld@@13 T@U) ) (! (let ((a@@93 (FieldTypeInv0 (type fld@@13))))
 (=> (and (and (= (type o@@68) refType) (= (type fld@@13) (FieldType a@@93))) (and (not (= o@@68 null)) (U_2_bool (MapType0Select (Reads2 t0@@47 t1@@23 t2@@4 h0@@14 f@@31 bx0@@20 bx1@@4) ($Box o@@68))))) (= (MapType1Select (MapType0Select h0@@14 o@@68) fld@@13) (MapType1Select (MapType0Select h1@@14 o@@68) fld@@13))))
 :qid |unknown.0:0|
 :skolemid |749|
 :no-pattern (type o@@68)
 :no-pattern (type fld@@13)
 :no-pattern (U_2_int o@@68)
 :no-pattern (U_2_bool o@@68)
 :no-pattern (U_2_int fld@@13)
 :no-pattern (U_2_bool fld@@13)
)))) (and (=> (Requires2 t0@@47 t1@@23 t2@@4 h0@@14 f@@31 bx0@@20 bx1@@4) (Requires2 t0@@47 t1@@23 t2@@4 h1@@14 f@@31 bx0@@20 bx1@@4)) (=> (Requires2 t0@@47 t1@@23 t2@@4 h1@@14 f@@31 bx0@@20 bx1@@4) (Requires2 t0@@47 t1@@23 t2@@4 h0@@14 f@@31 bx0@@20 bx1@@4))))
 :qid |unknown.0:0|
 :skolemid |750|
 :pattern ( ($HeapSucc h0@@14 h1@@14) (Requires2 t0@@47 t1@@23 t2@@4 h1@@14 f@@31 bx0@@20 bx1@@4))
)))
(assert (forall ((t0@@48 T@U) (t1@@24 T@U) (t2@@5 T@U) (h0@@15 T@U) (h1@@15 T@U) (f@@32 T@U) (bx0@@21 T@U) (bx1@@5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@48) TyType) (= (type t1@@24) TyType)) (= (type t2@@5) TyType)) (= (type h0@@15) (MapType0Type refType MapType1Type))) (= (type h1@@15) (MapType0Type refType MapType1Type))) (= (type f@@32) HandleTypeType)) (= (type bx0@@21) BoxType)) (= (type bx1@@5) BoxType)) (and (and (and ($HeapSucc h0@@15 h1@@15) (and ($IsGoodHeap h0@@15) ($IsGoodHeap h1@@15))) (and (and ($IsBox bx0@@21 t0@@48) ($IsBox bx1@@5 t1@@24)) ($Is f@@32 (Tclass._System.___hFunc2 t0@@48 t1@@24 t2@@5)))) (forall ((o@@69 T@U) (fld@@14 T@U) ) (! (let ((a@@94 (FieldTypeInv0 (type fld@@14))))
 (=> (and (and (= (type o@@69) refType) (= (type fld@@14) (FieldType a@@94))) (and (not (= o@@69 null)) (U_2_bool (MapType0Select (Reads2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5) ($Box o@@69))))) (= (MapType1Select (MapType0Select h0@@15 o@@69) fld@@14) (MapType1Select (MapType0Select h1@@15 o@@69) fld@@14))))
 :qid |unknown.0:0|
 :skolemid |751|
 :no-pattern (type o@@69)
 :no-pattern (type fld@@14)
 :no-pattern (U_2_int o@@69)
 :no-pattern (U_2_bool o@@69)
 :no-pattern (U_2_int fld@@14)
 :no-pattern (U_2_bool fld@@14)
)))) (and (=> (Requires2 t0@@48 t1@@24 t2@@5 h0@@15 f@@32 bx0@@21 bx1@@5) (Requires2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5)) (=> (Requires2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5) (Requires2 t0@@48 t1@@24 t2@@5 h0@@15 f@@32 bx0@@21 bx1@@5))))
 :qid |unknown.0:0|
 :skolemid |752|
 :pattern ( ($HeapSucc h0@@15 h1@@15) (Requires2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5))
)))
(assert (forall ((t0@@49 T@U) (t1@@25 T@U) (t2@@6 T@U) (h0@@16 T@U) (h1@@16 T@U) (f@@33 T@U) (bx0@@22 T@U) (bx1@@6 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@49) TyType) (= (type t1@@25) TyType)) (= (type t2@@6) TyType)) (= (type h0@@16) (MapType0Type refType MapType1Type))) (= (type h1@@16) (MapType0Type refType MapType1Type))) (= (type f@@33) HandleTypeType)) (= (type bx0@@22) BoxType)) (= (type bx1@@6) BoxType)) (and (and (and ($HeapSucc h0@@16 h1@@16) (and ($IsGoodHeap h0@@16) ($IsGoodHeap h1@@16))) (and (and ($IsBox bx0@@22 t0@@49) ($IsBox bx1@@6 t1@@25)) ($Is f@@33 (Tclass._System.___hFunc2 t0@@49 t1@@25 t2@@6)))) (forall ((o@@70 T@U) (fld@@15 T@U) ) (! (let ((a@@95 (FieldTypeInv0 (type fld@@15))))
 (=> (and (and (= (type o@@70) refType) (= (type fld@@15) (FieldType a@@95))) (and (not (= o@@70 null)) (U_2_bool (MapType0Select (Reads2 t0@@49 t1@@25 t2@@6 h0@@16 f@@33 bx0@@22 bx1@@6) ($Box o@@70))))) (= (MapType1Select (MapType0Select h0@@16 o@@70) fld@@15) (MapType1Select (MapType0Select h1@@16 o@@70) fld@@15))))
 :qid |unknown.0:0|
 :skolemid |753|
 :no-pattern (type o@@70)
 :no-pattern (type fld@@15)
 :no-pattern (U_2_int o@@70)
 :no-pattern (U_2_bool o@@70)
 :no-pattern (U_2_int fld@@15)
 :no-pattern (U_2_bool fld@@15)
)))) (= (Apply2 t0@@49 t1@@25 t2@@6 h0@@16 f@@33 bx0@@22 bx1@@6) (Apply2 t0@@49 t1@@25 t2@@6 h1@@16 f@@33 bx0@@22 bx1@@6)))
 :qid |unknown.0:0|
 :skolemid |754|
 :pattern ( ($HeapSucc h0@@16 h1@@16) (Apply2 t0@@49 t1@@25 t2@@6 h1@@16 f@@33 bx0@@22 bx1@@6))
)))
(assert (forall ((t0@@50 T@U) (t1@@26 T@U) (t2@@7 T@U) (h0@@17 T@U) (h1@@17 T@U) (f@@34 T@U) (bx0@@23 T@U) (bx1@@7 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@50) TyType) (= (type t1@@26) TyType)) (= (type t2@@7) TyType)) (= (type h0@@17) (MapType0Type refType MapType1Type))) (= (type h1@@17) (MapType0Type refType MapType1Type))) (= (type f@@34) HandleTypeType)) (= (type bx0@@23) BoxType)) (= (type bx1@@7) BoxType)) (and (and (and ($HeapSucc h0@@17 h1@@17) (and ($IsGoodHeap h0@@17) ($IsGoodHeap h1@@17))) (and (and ($IsBox bx0@@23 t0@@50) ($IsBox bx1@@7 t1@@26)) ($Is f@@34 (Tclass._System.___hFunc2 t0@@50 t1@@26 t2@@7)))) (forall ((o@@71 T@U) (fld@@16 T@U) ) (! (let ((a@@96 (FieldTypeInv0 (type fld@@16))))
 (=> (and (and (= (type o@@71) refType) (= (type fld@@16) (FieldType a@@96))) (and (not (= o@@71 null)) (U_2_bool (MapType0Select (Reads2 t0@@50 t1@@26 t2@@7 h1@@17 f@@34 bx0@@23 bx1@@7) ($Box o@@71))))) (= (MapType1Select (MapType0Select h0@@17 o@@71) fld@@16) (MapType1Select (MapType0Select h1@@17 o@@71) fld@@16))))
 :qid |unknown.0:0|
 :skolemid |755|
 :no-pattern (type o@@71)
 :no-pattern (type fld@@16)
 :no-pattern (U_2_int o@@71)
 :no-pattern (U_2_bool o@@71)
 :no-pattern (U_2_int fld@@16)
 :no-pattern (U_2_bool fld@@16)
)))) (= (Apply2 t0@@50 t1@@26 t2@@7 h0@@17 f@@34 bx0@@23 bx1@@7) (Apply2 t0@@50 t1@@26 t2@@7 h1@@17 f@@34 bx0@@23 bx1@@7)))
 :qid |unknown.0:0|
 :skolemid |756|
 :pattern ( ($HeapSucc h0@@17 h1@@17) (Apply2 t0@@50 t1@@26 t2@@7 h1@@17 f@@34 bx0@@23 bx1@@7))
)))
(assert (forall ((t0@@51 T@U) (t1@@27 T@U) (t2@@8 T@U) (heap@@14 T@U) (f@@35 T@U) (bx0@@24 T@U) (bx1@@8 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@51) TyType) (= (type t1@@27) TyType)) (= (type t2@@8) TyType)) (= (type heap@@14) (MapType0Type refType MapType1Type))) (= (type f@@35) HandleTypeType)) (= (type bx0@@24) BoxType)) (= (type bx1@@8) BoxType)) (and ($IsGoodHeap heap@@14) (and (and ($IsBox bx0@@24 t0@@51) ($IsBox bx1@@8 t1@@27)) ($Is f@@35 (Tclass._System.___hFunc2 t0@@51 t1@@27 t2@@8))))) (and (=> (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 $OneHeap f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 heap@@14 f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 heap@@14 f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 $OneHeap f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |757|
 :pattern ( (Reads2 t0@@51 t1@@27 t2@@8 $OneHeap f@@35 bx0@@24 bx1@@8) ($IsGoodHeap heap@@14))
 :pattern ( (Reads2 t0@@51 t1@@27 t2@@8 heap@@14 f@@35 bx0@@24 bx1@@8))
)))
(assert (forall ((t0@@52 T@U) (t1@@28 T@U) (t2@@9 T@U) (heap@@15 T@U) (f@@36 T@U) (bx0@@25 T@U) (bx1@@9 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@52) TyType) (= (type t1@@28) TyType)) (= (type t2@@9) TyType)) (= (type heap@@15) (MapType0Type refType MapType1Type))) (= (type f@@36) HandleTypeType)) (= (type bx0@@25) BoxType)) (= (type bx1@@9) BoxType)) (and (and ($IsGoodHeap heap@@15) (and (and ($IsBox bx0@@25 t0@@52) ($IsBox bx1@@9 t1@@28)) ($Is f@@36 (Tclass._System.___hFunc2 t0@@52 t1@@28 t2@@9)))) (|Set#Equal| (Reads2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9) (|Set#Empty| BoxType)))) (and (=> (Requires2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9) (Requires2 t0@@52 t1@@28 t2@@9 heap@@15 f@@36 bx0@@25 bx1@@9)) (=> (Requires2 t0@@52 t1@@28 t2@@9 heap@@15 f@@36 bx0@@25 bx1@@9) (Requires2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9))))
 :qid |unknown.0:0|
 :skolemid |758|
 :pattern ( (Requires2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9) ($IsGoodHeap heap@@15))
 :pattern ( (Requires2 t0@@52 t1@@28 t2@@9 heap@@15 f@@36 bx0@@25 bx1@@9))
)))
(assert (forall ((f@@37 T@U) (t0@@53 T@U) (t1@@29 T@U) (t2@@10 T@U) ) (!  (=> (and (and (and (= (type f@@37) HandleTypeType) (= (type t0@@53) TyType)) (= (type t1@@29) TyType)) (= (type t2@@10) TyType)) (and (=> ($Is f@@37 (Tclass._System.___hFunc2 t0@@53 t1@@29 t2@@10)) (forall ((h@@37 T@U) (bx0@@26 T@U) (bx1@@10 T@U) ) (!  (=> (and (and (and (= (type h@@37) (MapType0Type refType MapType1Type)) (= (type bx0@@26) BoxType)) (= (type bx1@@10) BoxType)) (and (and ($IsGoodHeap h@@37) (and ($IsBox bx0@@26 t0@@53) ($IsBox bx1@@10 t1@@29))) (Requires2 t0@@53 t1@@29 t2@@10 h@@37 f@@37 bx0@@26 bx1@@10))) ($IsBox (Apply2 t0@@53 t1@@29 t2@@10 h@@37 f@@37 bx0@@26 bx1@@10) t2@@10))
 :qid |DafnyPre.515:12|
 :skolemid |759|
 :pattern ( (Apply2 t0@@53 t1@@29 t2@@10 h@@37 f@@37 bx0@@26 bx1@@10))
))) (=> (forall ((h@@38 T@U) (bx0@@27 T@U) (bx1@@11 T@U) ) (!  (=> (and (and (and (= (type h@@38) (MapType0Type refType MapType1Type)) (= (type bx0@@27) BoxType)) (= (type bx1@@11) BoxType)) (and (and ($IsGoodHeap h@@38) (and ($IsBox bx0@@27 t0@@53) ($IsBox bx1@@11 t1@@29))) (Requires2 t0@@53 t1@@29 t2@@10 h@@38 f@@37 bx0@@27 bx1@@11))) ($IsBox (Apply2 t0@@53 t1@@29 t2@@10 h@@38 f@@37 bx0@@27 bx1@@11) t2@@10))
 :qid |DafnyPre.515:12|
 :skolemid |759|
 :pattern ( (Apply2 t0@@53 t1@@29 t2@@10 h@@38 f@@37 bx0@@27 bx1@@11))
)) ($Is f@@37 (Tclass._System.___hFunc2 t0@@53 t1@@29 t2@@10)))))
 :qid |unknown.0:0|
 :skolemid |760|
 :pattern ( ($Is f@@37 (Tclass._System.___hFunc2 t0@@53 t1@@29 t2@@10)))
)))
(assert (forall ((f@@38 T@U) (t0@@54 T@U) (t1@@30 T@U) (t2@@11 T@U) (u0@@1 T@U) (u1@@0 T@U) (u2 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type f@@38) HandleTypeType) (= (type t0@@54) TyType)) (= (type t1@@30) TyType)) (= (type t2@@11) TyType)) (= (type u0@@1) TyType)) (= (type u1@@0) TyType)) (= (type u2) TyType)) (and (and (and ($Is f@@38 (Tclass._System.___hFunc2 t0@@54 t1@@30 t2@@11)) (forall ((bx@@52 T@U) ) (!  (=> (and (= (type bx@@52) BoxType) ($IsBox bx@@52 u0@@1)) ($IsBox bx@@52 t0@@54))
 :qid |unknown.0:0|
 :skolemid |761|
 :pattern ( ($IsBox bx@@52 u0@@1))
 :pattern ( ($IsBox bx@@52 t0@@54))
))) (forall ((bx@@53 T@U) ) (!  (=> (and (= (type bx@@53) BoxType) ($IsBox bx@@53 u1@@0)) ($IsBox bx@@53 t1@@30))
 :qid |unknown.0:0|
 :skolemid |762|
 :pattern ( ($IsBox bx@@53 u1@@0))
 :pattern ( ($IsBox bx@@53 t1@@30))
))) (forall ((bx@@54 T@U) ) (!  (=> (and (= (type bx@@54) BoxType) ($IsBox bx@@54 t2@@11)) ($IsBox bx@@54 u2))
 :qid |unknown.0:0|
 :skolemid |763|
 :pattern ( ($IsBox bx@@54 t2@@11))
 :pattern ( ($IsBox bx@@54 u2))
)))) ($Is f@@38 (Tclass._System.___hFunc2 u0@@1 u1@@0 u2)))
 :qid |unknown.0:0|
 :skolemid |764|
 :pattern ( ($Is f@@38 (Tclass._System.___hFunc2 t0@@54 t1@@30 t2@@11)) ($Is f@@38 (Tclass._System.___hFunc2 u0@@1 u1@@0 u2)))
)))
(assert (forall ((f@@39 T@U) (t0@@55 T@U) (t1@@31 T@U) (t2@@12 T@U) (h@@39 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@39) HandleTypeType) (= (type t0@@55) TyType)) (= (type t1@@31) TyType)) (= (type t2@@12) TyType)) (= (type h@@39) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@39)) (and (=> ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@55 t1@@31 t2@@12) h@@39) (forall ((bx0@@28 T@U) (bx1@@12 T@U) ) (!  (=> (and (= (type bx0@@28) BoxType) (= (type bx1@@12) BoxType)) (=> (and (and (and ($IsBox bx0@@28 t0@@55) ($IsAllocBox bx0@@28 t0@@55 h@@39)) (and ($IsBox bx1@@12 t1@@31) ($IsAllocBox bx1@@12 t1@@31 h@@39))) (Requires2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12)) (forall ((r@@19 T@U) ) (!  (=> (= (type r@@19) refType) (=> (and (not (= r@@19 null)) (U_2_bool (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12) ($Box r@@19)))) (U_2_bool (MapType1Select (MapType0Select h@@39 r@@19) alloc))))
 :qid |unknown.0:0|
 :skolemid |765|
 :pattern ( (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12) ($Box r@@19)))
))))
 :qid |unknown.0:0|
 :skolemid |766|
 :pattern ( (Apply2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12))
 :pattern ( (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12))
))) (=> (forall ((bx0@@29 T@U) (bx1@@13 T@U) ) (!  (=> (and (= (type bx0@@29) BoxType) (= (type bx1@@13) BoxType)) (=> (and (and (and ($IsBox bx0@@29 t0@@55) ($IsAllocBox bx0@@29 t0@@55 h@@39)) (and ($IsBox bx1@@13 t1@@31) ($IsAllocBox bx1@@13 t1@@31 h@@39))) (Requires2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13)) (forall ((r@@20 T@U) ) (!  (=> (= (type r@@20) refType) (=> (and (not (= r@@20 null)) (U_2_bool (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13) ($Box r@@20)))) (U_2_bool (MapType1Select (MapType0Select h@@39 r@@20) alloc))))
 :qid |unknown.0:0|
 :skolemid |765|
 :pattern ( (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13) ($Box r@@20)))
))))
 :qid |unknown.0:0|
 :skolemid |766|
 :pattern ( (Apply2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13))
 :pattern ( (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13))
)) ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@55 t1@@31 t2@@12) h@@39))))
 :qid |unknown.0:0|
 :skolemid |767|
 :pattern ( ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@55 t1@@31 t2@@12) h@@39))
)))
(assert (forall ((f@@40 T@U) (t0@@56 T@U) (t1@@32 T@U) (t2@@13 T@U) (h@@40 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@40) HandleTypeType) (= (type t0@@56) TyType)) (= (type t1@@32) TyType)) (= (type t2@@13) TyType)) (= (type h@@40) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@40) ($IsAlloc f@@40 (Tclass._System.___hFunc2 t0@@56 t1@@32 t2@@13) h@@40))) (forall ((bx0@@30 T@U) (bx1@@14 T@U) ) (!  (=> (and (= (type bx0@@30) BoxType) (= (type bx1@@14) BoxType)) (=> (and (and ($IsAllocBox bx0@@30 t0@@56 h@@40) ($IsAllocBox bx1@@14 t1@@32 h@@40)) (Requires2 t0@@56 t1@@32 t2@@13 h@@40 f@@40 bx0@@30 bx1@@14)) ($IsAllocBox (Apply2 t0@@56 t1@@32 t2@@13 h@@40 f@@40 bx0@@30 bx1@@14) t2@@13 h@@40)))
 :qid |unknown.0:0|
 :skolemid |768|
 :pattern ( (Apply2 t0@@56 t1@@32 t2@@13 h@@40 f@@40 bx0@@30 bx1@@14))
)))
 :qid |unknown.0:0|
 :skolemid |769|
 :pattern ( ($IsAlloc f@@40 (Tclass._System.___hFunc2 t0@@56 t1@@32 t2@@13) h@@40))
)))
(assert (forall ((arg0@@152 T@U) (arg1@@72 T@U) (arg2@@30 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2 arg0@@152 arg1@@72 arg2@@30)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2|
 :pattern ( (Tclass._System.___hPartialFunc2 arg0@@152 arg1@@72 arg2@@30))
)))
(assert (forall ((|#$T0@@20| T@U) (|#$T1@@4| T@U) (|#$R@@33| T@U) ) (!  (=> (and (and (= (type |#$T0@@20|) TyType) (= (type |#$T1@@4|) TyType)) (= (type |#$R@@33|) TyType)) (= (Tag (Tclass._System.___hPartialFunc2 |#$T0@@20| |#$T1@@4| |#$R@@33|)) Tagclass._System.___hPartialFunc2))
 :qid |unknown.0:0|
 :skolemid |770|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@20| |#$T1@@4| |#$R@@33|))
)))
(assert (forall ((arg0@@153 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_0 arg0@@153)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_0|
 :pattern ( (Tclass._System.___hPartialFunc2_0 arg0@@153))
)))
(assert (forall ((|#$T0@@21| T@U) (|#$T1@@5| T@U) (|#$R@@34| T@U) ) (!  (=> (and (and (= (type |#$T0@@21|) TyType) (= (type |#$T1@@5|) TyType)) (= (type |#$R@@34|) TyType)) (= (Tclass._System.___hPartialFunc2_0 (Tclass._System.___hPartialFunc2 |#$T0@@21| |#$T1@@5| |#$R@@34|)) |#$T0@@21|))
 :qid |unknown.0:0|
 :skolemid |771|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@21| |#$T1@@5| |#$R@@34|))
)))
(assert (forall ((arg0@@154 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_1 arg0@@154)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_1|
 :pattern ( (Tclass._System.___hPartialFunc2_1 arg0@@154))
)))
(assert (forall ((|#$T0@@22| T@U) (|#$T1@@6| T@U) (|#$R@@35| T@U) ) (!  (=> (and (and (= (type |#$T0@@22|) TyType) (= (type |#$T1@@6|) TyType)) (= (type |#$R@@35|) TyType)) (= (Tclass._System.___hPartialFunc2_1 (Tclass._System.___hPartialFunc2 |#$T0@@22| |#$T1@@6| |#$R@@35|)) |#$T1@@6|))
 :qid |unknown.0:0|
 :skolemid |772|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@22| |#$T1@@6| |#$R@@35|))
)))
(assert (forall ((arg0@@155 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_2 arg0@@155)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_2|
 :pattern ( (Tclass._System.___hPartialFunc2_2 arg0@@155))
)))
(assert (forall ((|#$T0@@23| T@U) (|#$T1@@7| T@U) (|#$R@@36| T@U) ) (!  (=> (and (and (= (type |#$T0@@23|) TyType) (= (type |#$T1@@7|) TyType)) (= (type |#$R@@36|) TyType)) (= (Tclass._System.___hPartialFunc2_2 (Tclass._System.___hPartialFunc2 |#$T0@@23| |#$T1@@7| |#$R@@36|)) |#$R@@36|))
 :qid |unknown.0:0|
 :skolemid |773|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@23| |#$T1@@7| |#$R@@36|))
)))
(assert (forall ((|#$T0@@24| T@U) (|#$T1@@8| T@U) (|#$R@@37| T@U) (bx@@55 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@24|) TyType) (= (type |#$T1@@8|) TyType)) (= (type |#$R@@37|) TyType)) (= (type bx@@55) BoxType)) ($IsBox bx@@55 (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|))) (and (= ($Box ($Unbox HandleTypeType bx@@55)) bx@@55) ($Is ($Unbox HandleTypeType bx@@55) (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|))))
 :qid |unknown.0:0|
 :skolemid |774|
 :pattern ( ($IsBox bx@@55 (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|)))
)))
(assert (forall ((|#$T0@@25| T@U) (|#$T1@@9| T@U) (|#$R@@38| T@U) (|f#0@@7| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@25|) TyType) (= (type |#$T1@@9|) TyType)) (= (type |#$R@@38|) TyType)) (= (type |f#0@@7|) HandleTypeType)) (and (=> ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)) (and ($Is |f#0@@7| (Tclass._System.___hFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)) (forall ((|x0#0@@3| T@U) (|x1#0| T@U) ) (!  (=> (and (and (= (type |x0#0@@3|) BoxType) (= (type |x1#0|) BoxType)) (and ($IsBox |x0#0@@3| |#$T0@@25|) ($IsBox |x1#0| |#$T1@@9|))) (|Set#Equal| (Reads2 |#$T0@@25| |#$T1@@9| |#$R@@38| $OneHeap |f#0@@7| |x0#0@@3| |x1#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |775|
 :no-pattern (type |x0#0@@3|)
 :no-pattern (type |x1#0|)
 :no-pattern (U_2_int |x0#0@@3|)
 :no-pattern (U_2_bool |x0#0@@3|)
 :no-pattern (U_2_int |x1#0|)
 :no-pattern (U_2_bool |x1#0|)
)))) (=> (and ($Is |f#0@@7| (Tclass._System.___hFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)) (forall ((|x0#0@@4| T@U) (|x1#0@@0| T@U) ) (!  (=> (and (and (= (type |x0#0@@4|) BoxType) (= (type |x1#0@@0|) BoxType)) (and ($IsBox |x0#0@@4| |#$T0@@25|) ($IsBox |x1#0@@0| |#$T1@@9|))) (|Set#Equal| (Reads2 |#$T0@@25| |#$T1@@9| |#$R@@38| $OneHeap |f#0@@7| |x0#0@@4| |x1#0@@0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |775|
 :no-pattern (type |x0#0@@4|)
 :no-pattern (type |x1#0@@0|)
 :no-pattern (U_2_int |x0#0@@4|)
 :no-pattern (U_2_bool |x0#0@@4|)
 :no-pattern (U_2_int |x1#0@@0|)
 :no-pattern (U_2_bool |x1#0@@0|)
))) ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)))))
 :qid |unknown.0:0|
 :skolemid |776|
 :pattern ( ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)))
)))
(assert (forall ((|#$T0@@26| T@U) (|#$T1@@10| T@U) (|#$R@@39| T@U) (|f#0@@8| T@U) ($h@@11 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@26|) TyType) (= (type |#$T1@@10|) TyType)) (= (type |#$R@@39|) TyType)) (= (type |f#0@@8|) HandleTypeType)) (= (type $h@@11) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11) ($IsAlloc |f#0@@8| (Tclass._System.___hFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11)) (=> ($IsAlloc |f#0@@8| (Tclass._System.___hFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11) ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11))))
 :qid |unknown.0:0|
 :skolemid |777|
 :pattern ( ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11))
)))
(assert (forall ((arg0@@156 T@U) (arg1@@73 T@U) (arg2@@31 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2 arg0@@156 arg1@@73 arg2@@31)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2|
 :pattern ( (Tclass._System.___hTotalFunc2 arg0@@156 arg1@@73 arg2@@31))
)))
(assert (forall ((|#$T0@@27| T@U) (|#$T1@@11| T@U) (|#$R@@40| T@U) ) (!  (=> (and (and (= (type |#$T0@@27|) TyType) (= (type |#$T1@@11|) TyType)) (= (type |#$R@@40|) TyType)) (= (Tag (Tclass._System.___hTotalFunc2 |#$T0@@27| |#$T1@@11| |#$R@@40|)) Tagclass._System.___hTotalFunc2))
 :qid |unknown.0:0|
 :skolemid |778|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@27| |#$T1@@11| |#$R@@40|))
)))
(assert (forall ((arg0@@157 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_0 arg0@@157)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_0|
 :pattern ( (Tclass._System.___hTotalFunc2_0 arg0@@157))
)))
(assert (forall ((|#$T0@@28| T@U) (|#$T1@@12| T@U) (|#$R@@41| T@U) ) (!  (=> (and (and (= (type |#$T0@@28|) TyType) (= (type |#$T1@@12|) TyType)) (= (type |#$R@@41|) TyType)) (= (Tclass._System.___hTotalFunc2_0 (Tclass._System.___hTotalFunc2 |#$T0@@28| |#$T1@@12| |#$R@@41|)) |#$T0@@28|))
 :qid |unknown.0:0|
 :skolemid |779|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@28| |#$T1@@12| |#$R@@41|))
)))
(assert (forall ((arg0@@158 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_1 arg0@@158)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_1|
 :pattern ( (Tclass._System.___hTotalFunc2_1 arg0@@158))
)))
(assert (forall ((|#$T0@@29| T@U) (|#$T1@@13| T@U) (|#$R@@42| T@U) ) (!  (=> (and (and (= (type |#$T0@@29|) TyType) (= (type |#$T1@@13|) TyType)) (= (type |#$R@@42|) TyType)) (= (Tclass._System.___hTotalFunc2_1 (Tclass._System.___hTotalFunc2 |#$T0@@29| |#$T1@@13| |#$R@@42|)) |#$T1@@13|))
 :qid |unknown.0:0|
 :skolemid |780|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@29| |#$T1@@13| |#$R@@42|))
)))
(assert (forall ((arg0@@159 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_2 arg0@@159)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_2|
 :pattern ( (Tclass._System.___hTotalFunc2_2 arg0@@159))
)))
(assert (forall ((|#$T0@@30| T@U) (|#$T1@@14| T@U) (|#$R@@43| T@U) ) (!  (=> (and (and (= (type |#$T0@@30|) TyType) (= (type |#$T1@@14|) TyType)) (= (type |#$R@@43|) TyType)) (= (Tclass._System.___hTotalFunc2_2 (Tclass._System.___hTotalFunc2 |#$T0@@30| |#$T1@@14| |#$R@@43|)) |#$R@@43|))
 :qid |unknown.0:0|
 :skolemid |781|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@30| |#$T1@@14| |#$R@@43|))
)))
(assert (forall ((|#$T0@@31| T@U) (|#$T1@@15| T@U) (|#$R@@44| T@U) (bx@@56 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@31|) TyType) (= (type |#$T1@@15|) TyType)) (= (type |#$R@@44|) TyType)) (= (type bx@@56) BoxType)) ($IsBox bx@@56 (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|))) (and (= ($Box ($Unbox HandleTypeType bx@@56)) bx@@56) ($Is ($Unbox HandleTypeType bx@@56) (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|))))
 :qid |unknown.0:0|
 :skolemid |782|
 :pattern ( ($IsBox bx@@56 (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|)))
)))
(assert (forall ((|#$T0@@32| T@U) (|#$T1@@16| T@U) (|#$R@@45| T@U) (|f#0@@9| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@32|) TyType) (= (type |#$T1@@16|) TyType)) (= (type |#$R@@45|) TyType)) (= (type |f#0@@9|) HandleTypeType)) (and (=> ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)) (and ($Is |f#0@@9| (Tclass._System.___hPartialFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)) (forall ((|x0#0@@5| T@U) (|x1#0@@1| T@U) ) (!  (=> (and (and (= (type |x0#0@@5|) BoxType) (= (type |x1#0@@1|) BoxType)) (and ($IsBox |x0#0@@5| |#$T0@@32|) ($IsBox |x1#0@@1| |#$T1@@16|))) (Requires2 |#$T0@@32| |#$T1@@16| |#$R@@45| $OneHeap |f#0@@9| |x0#0@@5| |x1#0@@1|))
 :qid |unknown.0:0|
 :skolemid |783|
 :no-pattern (type |x0#0@@5|)
 :no-pattern (type |x1#0@@1|)
 :no-pattern (U_2_int |x0#0@@5|)
 :no-pattern (U_2_bool |x0#0@@5|)
 :no-pattern (U_2_int |x1#0@@1|)
 :no-pattern (U_2_bool |x1#0@@1|)
)))) (=> (and ($Is |f#0@@9| (Tclass._System.___hPartialFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)) (forall ((|x0#0@@6| T@U) (|x1#0@@2| T@U) ) (!  (=> (and (and (= (type |x0#0@@6|) BoxType) (= (type |x1#0@@2|) BoxType)) (and ($IsBox |x0#0@@6| |#$T0@@32|) ($IsBox |x1#0@@2| |#$T1@@16|))) (Requires2 |#$T0@@32| |#$T1@@16| |#$R@@45| $OneHeap |f#0@@9| |x0#0@@6| |x1#0@@2|))
 :qid |unknown.0:0|
 :skolemid |783|
 :no-pattern (type |x0#0@@6|)
 :no-pattern (type |x1#0@@2|)
 :no-pattern (U_2_int |x0#0@@6|)
 :no-pattern (U_2_bool |x0#0@@6|)
 :no-pattern (U_2_int |x1#0@@2|)
 :no-pattern (U_2_bool |x1#0@@2|)
))) ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)))))
 :qid |unknown.0:0|
 :skolemid |784|
 :pattern ( ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)))
)))
(assert (forall ((|#$T0@@33| T@U) (|#$T1@@17| T@U) (|#$R@@46| T@U) (|f#0@@10| T@U) ($h@@12 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@33|) TyType) (= (type |#$T1@@17|) TyType)) (= (type |#$R@@46|) TyType)) (= (type |f#0@@10|) HandleTypeType)) (= (type $h@@12) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12) ($IsAlloc |f#0@@10| (Tclass._System.___hPartialFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12)) (=> ($IsAlloc |f#0@@10| (Tclass._System.___hPartialFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12) ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12))))
 :qid |unknown.0:0|
 :skolemid |785|
 :pattern ( ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12))
)))
(assert  (and (forall ((arg0@@160 T@U) (arg1@@74 T@U) ) (! (= (type (|#_System._tuple#2._#Make2| arg0@@160 arg1@@74)) DatatypeTypeType)
 :qid |funType:#_System._tuple#2._#Make2|
 :pattern ( (|#_System._tuple#2._#Make2| arg0@@160 arg1@@74))
)) (forall ((arg0@@161 T@U) ) (! (= (type (DatatypeCtorId arg0@@161)) DtCtorIdType)
 :qid |funType:DatatypeCtorId|
 :pattern ( (DatatypeCtorId arg0@@161))
))))
(assert (forall ((|a#0#0#0| T@U) (|a#0#1#0| T@U) ) (!  (=> (and (= (type |a#0#0#0|) BoxType) (= (type |a#0#1#0|) BoxType)) (= (DatatypeCtorId (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|)) |##_System._tuple#2._#Make2|))
 :qid |unknown.0:0|
 :skolemid |786|
 :pattern ( (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|))
)))
(assert (forall ((d@@0 T@U) ) (!  (=> (= (type d@@0) DatatypeTypeType) (and (=> (_System.Tuple2.___hMake2_q d@@0) (= (DatatypeCtorId d@@0) |##_System._tuple#2._#Make2|)) (=> (= (DatatypeCtorId d@@0) |##_System._tuple#2._#Make2|) (_System.Tuple2.___hMake2_q d@@0))))
 :qid |unknown.0:0|
 :skolemid |787|
 :pattern ( (_System.Tuple2.___hMake2_q d@@0))
)))
(assert (forall ((d@@1 T@U) ) (!  (=> (and (= (type d@@1) DatatypeTypeType) (_System.Tuple2.___hMake2_q d@@1)) (exists ((|a#1#0#0| T@U) (|a#1#1#0| T@U) ) (!  (and (and (= (type |a#1#0#0|) BoxType) (= (type |a#1#1#0|) BoxType)) (= d@@1 (|#_System._tuple#2._#Make2| |a#1#0#0| |a#1#1#0|)))
 :qid |unknown.0:0|
 :skolemid |788|
 :no-pattern (type |a#1#0#0|)
 :no-pattern (type |a#1#1#0|)
 :no-pattern (U_2_int |a#1#0#0|)
 :no-pattern (U_2_bool |a#1#0#0|)
 :no-pattern (U_2_int |a#1#1#0|)
 :no-pattern (U_2_bool |a#1#1#0|)
)))
 :qid |unknown.0:0|
 :skolemid |789|
 :pattern ( (_System.Tuple2.___hMake2_q d@@1))
)))
(assert (forall ((arg0@@162 T@U) (arg1@@75 T@U) ) (! (= (type (Tclass._System.Tuple2 arg0@@162 arg1@@75)) TyType)
 :qid |funType:Tclass._System.Tuple2|
 :pattern ( (Tclass._System.Tuple2 arg0@@162 arg1@@75))
)))
(assert (forall ((|#$T0@@34| T@U) (|#$T1@@18| T@U) ) (!  (=> (and (= (type |#$T0@@34|) TyType) (= (type |#$T1@@18|) TyType)) (= (Tag (Tclass._System.Tuple2 |#$T0@@34| |#$T1@@18|)) Tagclass._System.Tuple2))
 :qid |unknown.0:0|
 :skolemid |790|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@34| |#$T1@@18|))
)))
(assert (forall ((arg0@@163 T@U) ) (! (= (type (Tclass._System.Tuple2_0 arg0@@163)) TyType)
 :qid |funType:Tclass._System.Tuple2_0|
 :pattern ( (Tclass._System.Tuple2_0 arg0@@163))
)))
(assert (forall ((|#$T0@@35| T@U) (|#$T1@@19| T@U) ) (!  (=> (and (= (type |#$T0@@35|) TyType) (= (type |#$T1@@19|) TyType)) (= (Tclass._System.Tuple2_0 (Tclass._System.Tuple2 |#$T0@@35| |#$T1@@19|)) |#$T0@@35|))
 :qid |unknown.0:0|
 :skolemid |791|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@35| |#$T1@@19|))
)))
(assert (forall ((arg0@@164 T@U) ) (! (= (type (Tclass._System.Tuple2_1 arg0@@164)) TyType)
 :qid |funType:Tclass._System.Tuple2_1|
 :pattern ( (Tclass._System.Tuple2_1 arg0@@164))
)))
(assert (forall ((|#$T0@@36| T@U) (|#$T1@@20| T@U) ) (!  (=> (and (= (type |#$T0@@36|) TyType) (= (type |#$T1@@20|) TyType)) (= (Tclass._System.Tuple2_1 (Tclass._System.Tuple2 |#$T0@@36| |#$T1@@20|)) |#$T1@@20|))
 :qid |unknown.0:0|
 :skolemid |792|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@36| |#$T1@@20|))
)))
(assert (forall ((|#$T0@@37| T@U) (|#$T1@@21| T@U) (bx@@57 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@37|) TyType) (= (type |#$T1@@21|) TyType)) (= (type bx@@57) BoxType)) ($IsBox bx@@57 (Tclass._System.Tuple2 |#$T0@@37| |#$T1@@21|))) (and (= ($Box ($Unbox DatatypeTypeType bx@@57)) bx@@57) ($Is ($Unbox DatatypeTypeType bx@@57) (Tclass._System.Tuple2 |#$T0@@37| |#$T1@@21|))))
 :qid |unknown.0:0|
 :skolemid |793|
 :pattern ( ($IsBox bx@@57 (Tclass._System.Tuple2 |#$T0@@37| |#$T1@@21|)))
)))
(assert (forall ((|#$T0@@38| T@U) (|#$T1@@22| T@U) (|a#2#0#0| T@U) (|a#2#1#0| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@38|) TyType) (= (type |#$T1@@22|) TyType)) (= (type |a#2#0#0|) BoxType)) (= (type |a#2#1#0|) BoxType)) (and (=> ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |#$T0@@38| |#$T1@@22|)) (and ($IsBox |a#2#0#0| |#$T0@@38|) ($IsBox |a#2#1#0| |#$T1@@22|))) (=> (and ($IsBox |a#2#0#0| |#$T0@@38|) ($IsBox |a#2#1#0| |#$T1@@22|)) ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |#$T0@@38| |#$T1@@22|)))))
 :qid |unknown.0:0|
 :skolemid |794|
 :pattern ( ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |#$T0@@38| |#$T1@@22|)))
)))
(assert (forall ((|#$T0@@39| T@U) (|#$T1@@23| T@U) (|a#3#0#0| T@U) (|a#3#1#0| T@U) ($h@@13 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@39|) TyType) (= (type |#$T1@@23|) TyType)) (= (type |a#3#0#0|) BoxType)) (= (type |a#3#1#0|) BoxType)) (= (type $h@@13) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@13)) (and (=> ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |#$T0@@39| |#$T1@@23|) $h@@13) (and ($IsAllocBox |a#3#0#0| |#$T0@@39| $h@@13) ($IsAllocBox |a#3#1#0| |#$T1@@23| $h@@13))) (=> (and ($IsAllocBox |a#3#0#0| |#$T0@@39| $h@@13) ($IsAllocBox |a#3#1#0| |#$T1@@23| $h@@13)) ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |#$T0@@39| |#$T1@@23|) $h@@13))))
 :qid |unknown.0:0|
 :skolemid |795|
 :pattern ( ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |#$T0@@39| |#$T1@@23|) $h@@13))
)))
(assert (forall ((d@@2 T@U) (|#$T0@@40| T@U) ($h@@14 T@U) ) (!  (=> (and (and (and (= (type d@@2) DatatypeTypeType) (= (type |#$T0@@40|) TyType)) (= (type $h@@14) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@14) (and (_System.Tuple2.___hMake2_q d@@2) (exists ((|#$T1@@24| T@U) ) (!  (and (= (type |#$T1@@24|) TyType) ($IsAlloc d@@2 (Tclass._System.Tuple2 |#$T0@@40| |#$T1@@24|) $h@@14))
 :qid |unknown.0:0|
 :skolemid |796|
 :pattern ( ($IsAlloc d@@2 (Tclass._System.Tuple2 |#$T0@@40| |#$T1@@24|) $h@@14))
))))) ($IsAllocBox (_System.Tuple2._0 d@@2) |#$T0@@40| $h@@14))
 :qid |unknown.0:0|
 :skolemid |797|
 :pattern ( ($IsAllocBox (_System.Tuple2._0 d@@2) |#$T0@@40| $h@@14))
)))
(assert (forall ((d@@3 T@U) (|#$T1@@25| T@U) ($h@@15 T@U) ) (!  (=> (and (and (and (= (type d@@3) DatatypeTypeType) (= (type |#$T1@@25|) TyType)) (= (type $h@@15) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@15) (and (_System.Tuple2.___hMake2_q d@@3) (exists ((|#$T0@@41| T@U) ) (!  (and (= (type |#$T0@@41|) TyType) ($IsAlloc d@@3 (Tclass._System.Tuple2 |#$T0@@41| |#$T1@@25|) $h@@15))
 :qid |unknown.0:0|
 :skolemid |798|
 :pattern ( ($IsAlloc d@@3 (Tclass._System.Tuple2 |#$T0@@41| |#$T1@@25|) $h@@15))
))))) ($IsAllocBox (_System.Tuple2._1 d@@3) |#$T1@@25| $h@@15))
 :qid |unknown.0:0|
 :skolemid |799|
 :pattern ( ($IsAllocBox (_System.Tuple2._1 d@@3) |#$T1@@25| $h@@15))
)))
(assert (forall ((|a#4#0#0| T@U) (|a#4#1#0| T@U) ) (!  (=> (and (= (type |a#4#0#0|) BoxType) (= (type |a#4#1#0|) BoxType)) (= (|#_System._tuple#2._#Make2| (Lit |a#4#0#0|) (Lit |a#4#1#0|)) (Lit (|#_System._tuple#2._#Make2| |a#4#0#0| |a#4#1#0|))))
 :qid |unknown.0:0|
 :skolemid |800|
 :pattern ( (|#_System._tuple#2._#Make2| (Lit |a#4#0#0|) (Lit |a#4#1#0|)))
)))
(assert (forall ((|a#5#0#0| T@U) (|a#5#1#0| T@U) ) (!  (=> (and (= (type |a#5#0#0|) BoxType) (= (type |a#5#1#0|) BoxType)) (= (_System.Tuple2._0 (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|)) |a#5#0#0|))
 :qid |unknown.0:0|
 :skolemid |801|
 :pattern ( (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|))
)))
(assert (forall ((|a#6#0#0| T@U) (|a#6#1#0| T@U) ) (!  (=> (and (= (type |a#6#0#0|) BoxType) (= (type |a#6#1#0|) BoxType)) (< (BoxRank |a#6#0#0|) (DtRank (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))))
 :qid |unknown.0:0|
 :skolemid |802|
 :pattern ( (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))
)))
(assert (forall ((|a#7#0#0| T@U) (|a#7#1#0| T@U) ) (!  (=> (and (= (type |a#7#0#0|) BoxType) (= (type |a#7#1#0|) BoxType)) (= (_System.Tuple2._1 (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|)) |a#7#1#0|))
 :qid |unknown.0:0|
 :skolemid |803|
 :pattern ( (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|))
)))
(assert (forall ((|a#8#0#0| T@U) (|a#8#1#0| T@U) ) (!  (=> (and (= (type |a#8#0#0|) BoxType) (= (type |a#8#1#0|) BoxType)) (< (BoxRank |a#8#1#0|) (DtRank (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|))))
 :qid |unknown.0:0|
 :skolemid |804|
 :pattern ( (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|))
)))
(assert (forall ((d@@4 T@U) ) (!  (=> (and (= (type d@@4) DatatypeTypeType) (|$IsA#_System.Tuple2| d@@4)) (_System.Tuple2.___hMake2_q d@@4))
 :qid |unknown.0:0|
 :skolemid |805|
 :pattern ( (|$IsA#_System.Tuple2| d@@4))
)))
(assert (forall ((|#$T0@@42| T@U) (|#$T1@@26| T@U) (d@@5 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@42|) TyType) (= (type |#$T1@@26|) TyType)) (= (type d@@5) DatatypeTypeType)) ($Is d@@5 (Tclass._System.Tuple2 |#$T0@@42| |#$T1@@26|))) (_System.Tuple2.___hMake2_q d@@5))
 :qid |unknown.0:0|
 :skolemid |806|
 :pattern ( (_System.Tuple2.___hMake2_q d@@5) ($Is d@@5 (Tclass._System.Tuple2 |#$T0@@42| |#$T1@@26|)))
)))
(assert (forall ((a@@97 T@U) (b@@58 T@U) ) (!  (=> (and (and (= (type a@@97) DatatypeTypeType) (= (type b@@58) DatatypeTypeType)) true) (and (=> (|_System.Tuple2#Equal| a@@97 b@@58) (and (= (_System.Tuple2._0 a@@97) (_System.Tuple2._0 b@@58)) (= (_System.Tuple2._1 a@@97) (_System.Tuple2._1 b@@58)))) (=> (and (= (_System.Tuple2._0 a@@97) (_System.Tuple2._0 b@@58)) (= (_System.Tuple2._1 a@@97) (_System.Tuple2._1 b@@58))) (|_System.Tuple2#Equal| a@@97 b@@58))))
 :qid |unknown.0:0|
 :skolemid |807|
 :pattern ( (|_System.Tuple2#Equal| a@@97 b@@58))
)))
(assert (forall ((a@@98 T@U) (b@@59 T@U) ) (!  (=> (and (= (type a@@98) DatatypeTypeType) (= (type b@@59) DatatypeTypeType)) (and (=> (|_System.Tuple2#Equal| a@@98 b@@59) (= a@@98 b@@59)) (=> (= a@@98 b@@59) (|_System.Tuple2#Equal| a@@98 b@@59))))
 :qid |unknown.0:0|
 :skolemid |808|
 :pattern ( (|_System.Tuple2#Equal| a@@98 b@@59))
)))
(assert (forall ((arg0@@165 T@U) (arg1@@76 T@U) (arg2@@32 T@U) (arg3@@12 T@U) ) (! (= (type (Tclass._System.___hFunc3 arg0@@165 arg1@@76 arg2@@32 arg3@@12)) TyType)
 :qid |funType:Tclass._System.___hFunc3|
 :pattern ( (Tclass._System.___hFunc3 arg0@@165 arg1@@76 arg2@@32 arg3@@12))
)))
(assert (forall ((|#$T0@@43| T@U) (|#$T1@@27| T@U) (|#$T2| T@U) (|#$R@@47| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@43|) TyType) (= (type |#$T1@@27|) TyType)) (= (type |#$T2|) TyType)) (= (type |#$R@@47|) TyType)) (= (Tag (Tclass._System.___hFunc3 |#$T0@@43| |#$T1@@27| |#$T2| |#$R@@47|)) Tagclass._System.___hFunc3))
 :qid |unknown.0:0|
 :skolemid |809|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@43| |#$T1@@27| |#$T2| |#$R@@47|))
)))
(assert (forall ((arg0@@166 T@U) ) (! (= (type (Tclass._System.___hFunc3_0 arg0@@166)) TyType)
 :qid |funType:Tclass._System.___hFunc3_0|
 :pattern ( (Tclass._System.___hFunc3_0 arg0@@166))
)))
(assert (forall ((|#$T0@@44| T@U) (|#$T1@@28| T@U) (|#$T2@@0| T@U) (|#$R@@48| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@44|) TyType) (= (type |#$T1@@28|) TyType)) (= (type |#$T2@@0|) TyType)) (= (type |#$R@@48|) TyType)) (= (Tclass._System.___hFunc3_0 (Tclass._System.___hFunc3 |#$T0@@44| |#$T1@@28| |#$T2@@0| |#$R@@48|)) |#$T0@@44|))
 :qid |unknown.0:0|
 :skolemid |810|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@44| |#$T1@@28| |#$T2@@0| |#$R@@48|))
)))
(assert (forall ((arg0@@167 T@U) ) (! (= (type (Tclass._System.___hFunc3_1 arg0@@167)) TyType)
 :qid |funType:Tclass._System.___hFunc3_1|
 :pattern ( (Tclass._System.___hFunc3_1 arg0@@167))
)))
(assert (forall ((|#$T0@@45| T@U) (|#$T1@@29| T@U) (|#$T2@@1| T@U) (|#$R@@49| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@45|) TyType) (= (type |#$T1@@29|) TyType)) (= (type |#$T2@@1|) TyType)) (= (type |#$R@@49|) TyType)) (= (Tclass._System.___hFunc3_1 (Tclass._System.___hFunc3 |#$T0@@45| |#$T1@@29| |#$T2@@1| |#$R@@49|)) |#$T1@@29|))
 :qid |unknown.0:0|
 :skolemid |811|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@45| |#$T1@@29| |#$T2@@1| |#$R@@49|))
)))
(assert (forall ((arg0@@168 T@U) ) (! (= (type (Tclass._System.___hFunc3_2 arg0@@168)) TyType)
 :qid |funType:Tclass._System.___hFunc3_2|
 :pattern ( (Tclass._System.___hFunc3_2 arg0@@168))
)))
(assert (forall ((|#$T0@@46| T@U) (|#$T1@@30| T@U) (|#$T2@@2| T@U) (|#$R@@50| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@46|) TyType) (= (type |#$T1@@30|) TyType)) (= (type |#$T2@@2|) TyType)) (= (type |#$R@@50|) TyType)) (= (Tclass._System.___hFunc3_2 (Tclass._System.___hFunc3 |#$T0@@46| |#$T1@@30| |#$T2@@2| |#$R@@50|)) |#$T2@@2|))
 :qid |unknown.0:0|
 :skolemid |812|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@46| |#$T1@@30| |#$T2@@2| |#$R@@50|))
)))
(assert (forall ((arg0@@169 T@U) ) (! (= (type (Tclass._System.___hFunc3_3 arg0@@169)) TyType)
 :qid |funType:Tclass._System.___hFunc3_3|
 :pattern ( (Tclass._System.___hFunc3_3 arg0@@169))
)))
(assert (forall ((|#$T0@@47| T@U) (|#$T1@@31| T@U) (|#$T2@@3| T@U) (|#$R@@51| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@47|) TyType) (= (type |#$T1@@31|) TyType)) (= (type |#$T2@@3|) TyType)) (= (type |#$R@@51|) TyType)) (= (Tclass._System.___hFunc3_3 (Tclass._System.___hFunc3 |#$T0@@47| |#$T1@@31| |#$T2@@3| |#$R@@51|)) |#$R@@51|))
 :qid |unknown.0:0|
 :skolemid |813|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@47| |#$T1@@31| |#$T2@@3| |#$R@@51|))
)))
(assert (forall ((|#$T0@@48| T@U) (|#$T1@@32| T@U) (|#$T2@@4| T@U) (|#$R@@52| T@U) (bx@@58 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@48|) TyType) (= (type |#$T1@@32|) TyType)) (= (type |#$T2@@4|) TyType)) (= (type |#$R@@52|) TyType)) (= (type bx@@58) BoxType)) ($IsBox bx@@58 (Tclass._System.___hFunc3 |#$T0@@48| |#$T1@@32| |#$T2@@4| |#$R@@52|))) (and (= ($Box ($Unbox HandleTypeType bx@@58)) bx@@58) ($Is ($Unbox HandleTypeType bx@@58) (Tclass._System.___hFunc3 |#$T0@@48| |#$T1@@32| |#$T2@@4| |#$R@@52|))))
 :qid |unknown.0:0|
 :skolemid |814|
 :pattern ( ($IsBox bx@@58 (Tclass._System.___hFunc3 |#$T0@@48| |#$T1@@32| |#$T2@@4| |#$R@@52|)))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (and (forall ((arg0@@170 T@T) (arg1@@77 T@T) (arg2@@33 T@T) (arg3@@13 T@T) (arg4@@4 T@T) ) (! (= (Ctor (MapType4Type arg0@@170 arg1@@77 arg2@@33 arg3@@13 arg4@@4)) 25)
 :qid |ctor:MapType4Type|
)) (forall ((arg0@@171 T@T) (arg1@@78 T@T) (arg2@@34 T@T) (arg3@@14 T@T) (arg4@@5 T@T) ) (! (= (MapType4TypeInv0 (MapType4Type arg0@@171 arg1@@78 arg2@@34 arg3@@14 arg4@@5)) arg0@@171)
 :qid |typeInv:MapType4TypeInv0|
 :pattern ( (MapType4Type arg0@@171 arg1@@78 arg2@@34 arg3@@14 arg4@@5))
))) (forall ((arg0@@172 T@T) (arg1@@79 T@T) (arg2@@35 T@T) (arg3@@15 T@T) (arg4@@6 T@T) ) (! (= (MapType4TypeInv1 (MapType4Type arg0@@172 arg1@@79 arg2@@35 arg3@@15 arg4@@6)) arg1@@79)
 :qid |typeInv:MapType4TypeInv1|
 :pattern ( (MapType4Type arg0@@172 arg1@@79 arg2@@35 arg3@@15 arg4@@6))
))) (forall ((arg0@@173 T@T) (arg1@@80 T@T) (arg2@@36 T@T) (arg3@@16 T@T) (arg4@@7 T@T) ) (! (= (MapType4TypeInv2 (MapType4Type arg0@@173 arg1@@80 arg2@@36 arg3@@16 arg4@@7)) arg2@@36)
 :qid |typeInv:MapType4TypeInv2|
 :pattern ( (MapType4Type arg0@@173 arg1@@80 arg2@@36 arg3@@16 arg4@@7))
))) (forall ((arg0@@174 T@T) (arg1@@81 T@T) (arg2@@37 T@T) (arg3@@17 T@T) (arg4@@8 T@T) ) (! (= (MapType4TypeInv3 (MapType4Type arg0@@174 arg1@@81 arg2@@37 arg3@@17 arg4@@8)) arg3@@17)
 :qid |typeInv:MapType4TypeInv3|
 :pattern ( (MapType4Type arg0@@174 arg1@@81 arg2@@37 arg3@@17 arg4@@8))
))) (forall ((arg0@@175 T@T) (arg1@@82 T@T) (arg2@@38 T@T) (arg3@@18 T@T) (arg4@@9 T@T) ) (! (= (MapType4TypeInv4 (MapType4Type arg0@@175 arg1@@82 arg2@@38 arg3@@18 arg4@@9)) arg4@@9)
 :qid |typeInv:MapType4TypeInv4|
 :pattern ( (MapType4Type arg0@@175 arg1@@82 arg2@@38 arg3@@18 arg4@@9))
))) (forall ((arg0@@176 T@U) (arg1@@83 T@U) (arg2@@39 T@U) (arg3@@19 T@U) (arg4@@10 T@U) ) (! (let ((aVar4 (MapType4TypeInv4 (type arg0@@176))))
(= (type (MapType4Select arg0@@176 arg1@@83 arg2@@39 arg3@@19 arg4@@10)) aVar4))
 :qid |funType:MapType4Select|
 :pattern ( (MapType4Select arg0@@176 arg1@@83 arg2@@39 arg3@@19 arg4@@10))
))) (forall ((arg0@@177 T@U) (arg1@@84 T@U) (arg2@@40 T@U) (arg3@@20 T@U) (arg4@@11 T@U) (arg5@@1 T@U) ) (! (let ((aVar4@@0 (type arg5@@1)))
(let ((aVar3@@2 (type arg4@@11)))
(let ((aVar2@@3 (type arg3@@20)))
(let ((aVar1@@4 (type arg2@@40)))
(let ((aVar0@@2 (type arg1@@84)))
(= (type (MapType4Store arg0@@177 arg1@@84 arg2@@40 arg3@@20 arg4@@11 arg5@@1)) (MapType4Type aVar0@@2 aVar1@@4 aVar2@@3 aVar3@@2 aVar4@@0)))))))
 :qid |funType:MapType4Store|
 :pattern ( (MapType4Store arg0@@177 arg1@@84 arg2@@40 arg3@@20 arg4@@11 arg5@@1))
))) (forall ((m@@36 T@U) (x0@@14 T@U) (x1@@8 T@U) (x2@@4 T@U) (x3 T@U) (val@@15 T@U) ) (! (let ((aVar4@@1 (MapType4TypeInv4 (type m@@36))))
 (=> (= (type val@@15) aVar4@@1) (= (MapType4Select (MapType4Store m@@36 x0@@14 x1@@8 x2@@4 x3 val@@15) x0@@14 x1@@8 x2@@4 x3) val@@15)))
 :qid |mapAx0:MapType4Select|
 :weight 0
))) (and (and (and (and (forall ((val@@16 T@U) (m@@37 T@U) (x0@@15 T@U) (x1@@9 T@U) (x2@@5 T@U) (x3@@0 T@U) (y0@@10 T@U) (y1@@6 T@U) (y2@@3 T@U) (y3 T@U) ) (!  (or (= x0@@15 y0@@10) (= (MapType4Select (MapType4Store m@@37 x0@@15 x1@@9 x2@@5 x3@@0 val@@16) y0@@10 y1@@6 y2@@3 y3) (MapType4Select m@@37 y0@@10 y1@@6 y2@@3 y3)))
 :qid |mapAx1:MapType4Select:0|
 :weight 0
)) (forall ((val@@17 T@U) (m@@38 T@U) (x0@@16 T@U) (x1@@10 T@U) (x2@@6 T@U) (x3@@1 T@U) (y0@@11 T@U) (y1@@7 T@U) (y2@@4 T@U) (y3@@0 T@U) ) (!  (or (= x1@@10 y1@@7) (= (MapType4Select (MapType4Store m@@38 x0@@16 x1@@10 x2@@6 x3@@1 val@@17) y0@@11 y1@@7 y2@@4 y3@@0) (MapType4Select m@@38 y0@@11 y1@@7 y2@@4 y3@@0)))
 :qid |mapAx1:MapType4Select:1|
 :weight 0
))) (forall ((val@@18 T@U) (m@@39 T@U) (x0@@17 T@U) (x1@@11 T@U) (x2@@7 T@U) (x3@@2 T@U) (y0@@12 T@U) (y1@@8 T@U) (y2@@5 T@U) (y3@@1 T@U) ) (!  (or (= x2@@7 y2@@5) (= (MapType4Select (MapType4Store m@@39 x0@@17 x1@@11 x2@@7 x3@@2 val@@18) y0@@12 y1@@8 y2@@5 y3@@1) (MapType4Select m@@39 y0@@12 y1@@8 y2@@5 y3@@1)))
 :qid |mapAx1:MapType4Select:2|
 :weight 0
))) (forall ((val@@19 T@U) (m@@40 T@U) (x0@@18 T@U) (x1@@12 T@U) (x2@@8 T@U) (x3@@3 T@U) (y0@@13 T@U) (y1@@9 T@U) (y2@@6 T@U) (y3@@2 T@U) ) (!  (or (= x3@@3 y3@@2) (= (MapType4Select (MapType4Store m@@40 x0@@18 x1@@12 x2@@8 x3@@3 val@@19) y0@@13 y1@@9 y2@@6 y3@@2) (MapType4Select m@@40 y0@@13 y1@@9 y2@@6 y3@@2)))
 :qid |mapAx1:MapType4Select:3|
 :weight 0
))) (forall ((val@@20 T@U) (m@@41 T@U) (x0@@19 T@U) (x1@@13 T@U) (x2@@9 T@U) (x3@@4 T@U) (y0@@14 T@U) (y1@@10 T@U) (y2@@7 T@U) (y3@@3 T@U) ) (!  (or true (= (MapType4Select (MapType4Store m@@41 x0@@19 x1@@13 x2@@9 x3@@4 val@@20) y0@@14 y1@@10 y2@@7 y3@@3) (MapType4Select m@@41 y0@@14 y1@@10 y2@@7 y3@@3)))
 :qid |mapAx2:MapType4Select|
 :weight 0
)))) (forall ((arg0@@178 T@U) (arg1@@85 T@U) (arg2@@41 T@U) (arg3@@21 T@U) (arg4@@12 T@U) (arg5@@2 T@U) (arg6@@1 T@U) (arg7 T@U) (arg8 T@U) ) (! (= (type (Apply3 arg0@@178 arg1@@85 arg2@@41 arg3@@21 arg4@@12 arg5@@2 arg6@@1 arg7 arg8)) BoxType)
 :qid |funType:Apply3|
 :pattern ( (Apply3 arg0@@178 arg1@@85 arg2@@41 arg3@@21 arg4@@12 arg5@@2 arg6@@1 arg7 arg8))
))) (forall ((arg0@@179 T@U) (arg1@@86 T@U) (arg2@@42 T@U) ) (! (= (type (Handle3 arg0@@179 arg1@@86 arg2@@42)) HandleTypeType)
 :qid |funType:Handle3|
 :pattern ( (Handle3 arg0@@179 arg1@@86 arg2@@42))
))))
(assert (forall ((t0@@57 T@U) (t1@@33 T@U) (t2@@14 T@U) (t3 T@U) (heap@@16 T@U) (h@@41 T@U) (r@@21 T@U) (rd@@8 T@U) (bx0@@31 T@U) (bx1@@15 T@U) (bx2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@57) TyType) (= (type t1@@33) TyType)) (= (type t2@@14) TyType)) (= (type t3) TyType)) (= (type heap@@16) (MapType0Type refType MapType1Type))) (= (type h@@41) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType))) (= (type r@@21) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType boolType))) (= (type rd@@8) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@31) BoxType)) (= (type bx1@@15) BoxType)) (= (type bx2) BoxType)) (= (Apply3 t0@@57 t1@@33 t2@@14 t3 heap@@16 (Handle3 h@@41 r@@21 rd@@8) bx0@@31 bx1@@15 bx2) (MapType4Select h@@41 heap@@16 bx0@@31 bx1@@15 bx2)))
 :qid |unknown.0:0|
 :skolemid |815|
 :pattern ( (Apply3 t0@@57 t1@@33 t2@@14 t3 heap@@16 (Handle3 h@@41 r@@21 rd@@8) bx0@@31 bx1@@15 bx2))
)))
(assert (forall ((t0@@58 T@U) (t1@@34 T@U) (t2@@15 T@U) (t3@@0 T@U) (heap@@17 T@U) (h@@42 T@U) (r@@22 T@U) (rd@@9 T@U) (bx0@@32 T@U) (bx1@@16 T@U) (bx2@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@58) TyType) (= (type t1@@34) TyType)) (= (type t2@@15) TyType)) (= (type t3@@0) TyType)) (= (type heap@@17) (MapType0Type refType MapType1Type))) (= (type h@@42) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType))) (= (type r@@22) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType boolType))) (= (type rd@@9) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@32) BoxType)) (= (type bx1@@16) BoxType)) (= (type bx2@@0) BoxType)) (U_2_bool (MapType4Select r@@22 heap@@17 bx0@@32 bx1@@16 bx2@@0))) (Requires3 t0@@58 t1@@34 t2@@15 t3@@0 heap@@17 (Handle3 h@@42 r@@22 rd@@9) bx0@@32 bx1@@16 bx2@@0))
 :qid |unknown.0:0|
 :skolemid |816|
 :pattern ( (Requires3 t0@@58 t1@@34 t2@@15 t3@@0 heap@@17 (Handle3 h@@42 r@@22 rd@@9) bx0@@32 bx1@@16 bx2@@0))
)))
(assert (forall ((arg0@@180 T@U) (arg1@@87 T@U) (arg2@@43 T@U) (arg3@@22 T@U) (arg4@@13 T@U) (arg5@@3 T@U) (arg6@@2 T@U) (arg7@@0 T@U) (arg8@@0 T@U) ) (! (= (type (Reads3 arg0@@180 arg1@@87 arg2@@43 arg3@@22 arg4@@13 arg5@@3 arg6@@2 arg7@@0 arg8@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads3|
 :pattern ( (Reads3 arg0@@180 arg1@@87 arg2@@43 arg3@@22 arg4@@13 arg5@@3 arg6@@2 arg7@@0 arg8@@0))
)))
(assert (forall ((t0@@59 T@U) (t1@@35 T@U) (t2@@16 T@U) (t3@@1 T@U) (heap@@18 T@U) (h@@43 T@U) (r@@23 T@U) (rd@@10 T@U) (bx0@@33 T@U) (bx1@@17 T@U) (bx2@@1 T@U) (bx@@59 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@59) TyType) (= (type t1@@35) TyType)) (= (type t2@@16) TyType)) (= (type t3@@1) TyType)) (= (type heap@@18) (MapType0Type refType MapType1Type))) (= (type h@@43) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType))) (= (type r@@23) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType boolType))) (= (type rd@@10) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@33) BoxType)) (= (type bx1@@17) BoxType)) (= (type bx2@@1) BoxType)) (= (type bx@@59) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads3 t0@@59 t1@@35 t2@@16 t3@@1 heap@@18 (Handle3 h@@43 r@@23 rd@@10) bx0@@33 bx1@@17 bx2@@1) bx@@59)) (U_2_bool (MapType0Select (MapType4Select rd@@10 heap@@18 bx0@@33 bx1@@17 bx2@@1) bx@@59))) (=> (U_2_bool (MapType0Select (MapType4Select rd@@10 heap@@18 bx0@@33 bx1@@17 bx2@@1) bx@@59)) (U_2_bool (MapType0Select (Reads3 t0@@59 t1@@35 t2@@16 t3@@1 heap@@18 (Handle3 h@@43 r@@23 rd@@10) bx0@@33 bx1@@17 bx2@@1) bx@@59)))))
 :qid |unknown.0:0|
 :skolemid |817|
 :pattern ( (MapType0Select (Reads3 t0@@59 t1@@35 t2@@16 t3@@1 heap@@18 (Handle3 h@@43 r@@23 rd@@10) bx0@@33 bx1@@17 bx2@@1) bx@@59))
)))
(assert (forall ((t0@@60 T@U) (t1@@36 T@U) (t2@@17 T@U) (t3@@2 T@U) (h0@@18 T@U) (h1@@18 T@U) (f@@41 T@U) (bx0@@34 T@U) (bx1@@18 T@U) (bx2@@2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@60) TyType) (= (type t1@@36) TyType)) (= (type t2@@17) TyType)) (= (type t3@@2) TyType)) (= (type h0@@18) (MapType0Type refType MapType1Type))) (= (type h1@@18) (MapType0Type refType MapType1Type))) (= (type f@@41) HandleTypeType)) (= (type bx0@@34) BoxType)) (= (type bx1@@18) BoxType)) (= (type bx2@@2) BoxType)) (and (and (and ($HeapSucc h0@@18 h1@@18) (and ($IsGoodHeap h0@@18) ($IsGoodHeap h1@@18))) (and (and (and ($IsBox bx0@@34 t0@@60) ($IsBox bx1@@18 t1@@36)) ($IsBox bx2@@2 t2@@17)) ($Is f@@41 (Tclass._System.___hFunc3 t0@@60 t1@@36 t2@@17 t3@@2)))) (forall ((o@@72 T@U) (fld@@17 T@U) ) (! (let ((a@@99 (FieldTypeInv0 (type fld@@17))))
 (=> (and (and (= (type o@@72) refType) (= (type fld@@17) (FieldType a@@99))) (and (not (= o@@72 null)) (U_2_bool (MapType0Select (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h0@@18 f@@41 bx0@@34 bx1@@18 bx2@@2) ($Box o@@72))))) (= (MapType1Select (MapType0Select h0@@18 o@@72) fld@@17) (MapType1Select (MapType0Select h1@@18 o@@72) fld@@17))))
 :qid |unknown.0:0|
 :skolemid |818|
 :no-pattern (type o@@72)
 :no-pattern (type fld@@17)
 :no-pattern (U_2_int o@@72)
 :no-pattern (U_2_bool o@@72)
 :no-pattern (U_2_int fld@@17)
 :no-pattern (U_2_bool fld@@17)
)))) (= (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h0@@18 f@@41 bx0@@34 bx1@@18 bx2@@2) (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h1@@18 f@@41 bx0@@34 bx1@@18 bx2@@2)))
 :qid |unknown.0:0|
 :skolemid |819|
 :pattern ( ($HeapSucc h0@@18 h1@@18) (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h1@@18 f@@41 bx0@@34 bx1@@18 bx2@@2))
)))
(assert (forall ((t0@@61 T@U) (t1@@37 T@U) (t2@@18 T@U) (t3@@3 T@U) (h0@@19 T@U) (h1@@19 T@U) (f@@42 T@U) (bx0@@35 T@U) (bx1@@19 T@U) (bx2@@3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@61) TyType) (= (type t1@@37) TyType)) (= (type t2@@18) TyType)) (= (type t3@@3) TyType)) (= (type h0@@19) (MapType0Type refType MapType1Type))) (= (type h1@@19) (MapType0Type refType MapType1Type))) (= (type f@@42) HandleTypeType)) (= (type bx0@@35) BoxType)) (= (type bx1@@19) BoxType)) (= (type bx2@@3) BoxType)) (and (and (and ($HeapSucc h0@@19 h1@@19) (and ($IsGoodHeap h0@@19) ($IsGoodHeap h1@@19))) (and (and (and ($IsBox bx0@@35 t0@@61) ($IsBox bx1@@19 t1@@37)) ($IsBox bx2@@3 t2@@18)) ($Is f@@42 (Tclass._System.___hFunc3 t0@@61 t1@@37 t2@@18 t3@@3)))) (forall ((o@@73 T@U) (fld@@18 T@U) ) (! (let ((a@@100 (FieldTypeInv0 (type fld@@18))))
 (=> (and (and (= (type o@@73) refType) (= (type fld@@18) (FieldType a@@100))) (and (not (= o@@73 null)) (U_2_bool (MapType0Select (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h1@@19 f@@42 bx0@@35 bx1@@19 bx2@@3) ($Box o@@73))))) (= (MapType1Select (MapType0Select h0@@19 o@@73) fld@@18) (MapType1Select (MapType0Select h1@@19 o@@73) fld@@18))))
 :qid |unknown.0:0|
 :skolemid |820|
 :no-pattern (type o@@73)
 :no-pattern (type fld@@18)
 :no-pattern (U_2_int o@@73)
 :no-pattern (U_2_bool o@@73)
 :no-pattern (U_2_int fld@@18)
 :no-pattern (U_2_bool fld@@18)
)))) (= (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h0@@19 f@@42 bx0@@35 bx1@@19 bx2@@3) (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h1@@19 f@@42 bx0@@35 bx1@@19 bx2@@3)))
 :qid |unknown.0:0|
 :skolemid |821|
 :pattern ( ($HeapSucc h0@@19 h1@@19) (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h1@@19 f@@42 bx0@@35 bx1@@19 bx2@@3))
)))
(assert (forall ((t0@@62 T@U) (t1@@38 T@U) (t2@@19 T@U) (t3@@4 T@U) (h0@@20 T@U) (h1@@20 T@U) (f@@43 T@U) (bx0@@36 T@U) (bx1@@20 T@U) (bx2@@4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@62) TyType) (= (type t1@@38) TyType)) (= (type t2@@19) TyType)) (= (type t3@@4) TyType)) (= (type h0@@20) (MapType0Type refType MapType1Type))) (= (type h1@@20) (MapType0Type refType MapType1Type))) (= (type f@@43) HandleTypeType)) (= (type bx0@@36) BoxType)) (= (type bx1@@20) BoxType)) (= (type bx2@@4) BoxType)) (and (and (and ($HeapSucc h0@@20 h1@@20) (and ($IsGoodHeap h0@@20) ($IsGoodHeap h1@@20))) (and (and (and ($IsBox bx0@@36 t0@@62) ($IsBox bx1@@20 t1@@38)) ($IsBox bx2@@4 t2@@19)) ($Is f@@43 (Tclass._System.___hFunc3 t0@@62 t1@@38 t2@@19 t3@@4)))) (forall ((o@@74 T@U) (fld@@19 T@U) ) (! (let ((a@@101 (FieldTypeInv0 (type fld@@19))))
 (=> (and (and (= (type o@@74) refType) (= (type fld@@19) (FieldType a@@101))) (and (not (= o@@74 null)) (U_2_bool (MapType0Select (Reads3 t0@@62 t1@@38 t2@@19 t3@@4 h0@@20 f@@43 bx0@@36 bx1@@20 bx2@@4) ($Box o@@74))))) (= (MapType1Select (MapType0Select h0@@20 o@@74) fld@@19) (MapType1Select (MapType0Select h1@@20 o@@74) fld@@19))))
 :qid |unknown.0:0|
 :skolemid |822|
 :no-pattern (type o@@74)
 :no-pattern (type fld@@19)
 :no-pattern (U_2_int o@@74)
 :no-pattern (U_2_bool o@@74)
 :no-pattern (U_2_int fld@@19)
 :no-pattern (U_2_bool fld@@19)
)))) (and (=> (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h0@@20 f@@43 bx0@@36 bx1@@20 bx2@@4) (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h1@@20 f@@43 bx0@@36 bx1@@20 bx2@@4)) (=> (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h1@@20 f@@43 bx0@@36 bx1@@20 bx2@@4) (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h0@@20 f@@43 bx0@@36 bx1@@20 bx2@@4))))
 :qid |unknown.0:0|
 :skolemid |823|
 :pattern ( ($HeapSucc h0@@20 h1@@20) (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h1@@20 f@@43 bx0@@36 bx1@@20 bx2@@4))
)))
(assert (forall ((t0@@63 T@U) (t1@@39 T@U) (t2@@20 T@U) (t3@@5 T@U) (h0@@21 T@U) (h1@@21 T@U) (f@@44 T@U) (bx0@@37 T@U) (bx1@@21 T@U) (bx2@@5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@63) TyType) (= (type t1@@39) TyType)) (= (type t2@@20) TyType)) (= (type t3@@5) TyType)) (= (type h0@@21) (MapType0Type refType MapType1Type))) (= (type h1@@21) (MapType0Type refType MapType1Type))) (= (type f@@44) HandleTypeType)) (= (type bx0@@37) BoxType)) (= (type bx1@@21) BoxType)) (= (type bx2@@5) BoxType)) (and (and (and ($HeapSucc h0@@21 h1@@21) (and ($IsGoodHeap h0@@21) ($IsGoodHeap h1@@21))) (and (and (and ($IsBox bx0@@37 t0@@63) ($IsBox bx1@@21 t1@@39)) ($IsBox bx2@@5 t2@@20)) ($Is f@@44 (Tclass._System.___hFunc3 t0@@63 t1@@39 t2@@20 t3@@5)))) (forall ((o@@75 T@U) (fld@@20 T@U) ) (! (let ((a@@102 (FieldTypeInv0 (type fld@@20))))
 (=> (and (and (= (type o@@75) refType) (= (type fld@@20) (FieldType a@@102))) (and (not (= o@@75 null)) (U_2_bool (MapType0Select (Reads3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5) ($Box o@@75))))) (= (MapType1Select (MapType0Select h0@@21 o@@75) fld@@20) (MapType1Select (MapType0Select h1@@21 o@@75) fld@@20))))
 :qid |unknown.0:0|
 :skolemid |824|
 :no-pattern (type o@@75)
 :no-pattern (type fld@@20)
 :no-pattern (U_2_int o@@75)
 :no-pattern (U_2_bool o@@75)
 :no-pattern (U_2_int fld@@20)
 :no-pattern (U_2_bool fld@@20)
)))) (and (=> (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h0@@21 f@@44 bx0@@37 bx1@@21 bx2@@5) (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5)) (=> (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5) (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h0@@21 f@@44 bx0@@37 bx1@@21 bx2@@5))))
 :qid |unknown.0:0|
 :skolemid |825|
 :pattern ( ($HeapSucc h0@@21 h1@@21) (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5))
)))
(assert (forall ((t0@@64 T@U) (t1@@40 T@U) (t2@@21 T@U) (t3@@6 T@U) (h0@@22 T@U) (h1@@22 T@U) (f@@45 T@U) (bx0@@38 T@U) (bx1@@22 T@U) (bx2@@6 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@64) TyType) (= (type t1@@40) TyType)) (= (type t2@@21) TyType)) (= (type t3@@6) TyType)) (= (type h0@@22) (MapType0Type refType MapType1Type))) (= (type h1@@22) (MapType0Type refType MapType1Type))) (= (type f@@45) HandleTypeType)) (= (type bx0@@38) BoxType)) (= (type bx1@@22) BoxType)) (= (type bx2@@6) BoxType)) (and (and (and ($HeapSucc h0@@22 h1@@22) (and ($IsGoodHeap h0@@22) ($IsGoodHeap h1@@22))) (and (and (and ($IsBox bx0@@38 t0@@64) ($IsBox bx1@@22 t1@@40)) ($IsBox bx2@@6 t2@@21)) ($Is f@@45 (Tclass._System.___hFunc3 t0@@64 t1@@40 t2@@21 t3@@6)))) (forall ((o@@76 T@U) (fld@@21 T@U) ) (! (let ((a@@103 (FieldTypeInv0 (type fld@@21))))
 (=> (and (and (= (type o@@76) refType) (= (type fld@@21) (FieldType a@@103))) (and (not (= o@@76 null)) (U_2_bool (MapType0Select (Reads3 t0@@64 t1@@40 t2@@21 t3@@6 h0@@22 f@@45 bx0@@38 bx1@@22 bx2@@6) ($Box o@@76))))) (= (MapType1Select (MapType0Select h0@@22 o@@76) fld@@21) (MapType1Select (MapType0Select h1@@22 o@@76) fld@@21))))
 :qid |unknown.0:0|
 :skolemid |826|
 :no-pattern (type o@@76)
 :no-pattern (type fld@@21)
 :no-pattern (U_2_int o@@76)
 :no-pattern (U_2_bool o@@76)
 :no-pattern (U_2_int fld@@21)
 :no-pattern (U_2_bool fld@@21)
)))) (= (Apply3 t0@@64 t1@@40 t2@@21 t3@@6 h0@@22 f@@45 bx0@@38 bx1@@22 bx2@@6) (Apply3 t0@@64 t1@@40 t2@@21 t3@@6 h1@@22 f@@45 bx0@@38 bx1@@22 bx2@@6)))
 :qid |unknown.0:0|
 :skolemid |827|
 :pattern ( ($HeapSucc h0@@22 h1@@22) (Apply3 t0@@64 t1@@40 t2@@21 t3@@6 h1@@22 f@@45 bx0@@38 bx1@@22 bx2@@6))
)))
(assert (forall ((t0@@65 T@U) (t1@@41 T@U) (t2@@22 T@U) (t3@@7 T@U) (h0@@23 T@U) (h1@@23 T@U) (f@@46 T@U) (bx0@@39 T@U) (bx1@@23 T@U) (bx2@@7 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@65) TyType) (= (type t1@@41) TyType)) (= (type t2@@22) TyType)) (= (type t3@@7) TyType)) (= (type h0@@23) (MapType0Type refType MapType1Type))) (= (type h1@@23) (MapType0Type refType MapType1Type))) (= (type f@@46) HandleTypeType)) (= (type bx0@@39) BoxType)) (= (type bx1@@23) BoxType)) (= (type bx2@@7) BoxType)) (and (and (and ($HeapSucc h0@@23 h1@@23) (and ($IsGoodHeap h0@@23) ($IsGoodHeap h1@@23))) (and (and (and ($IsBox bx0@@39 t0@@65) ($IsBox bx1@@23 t1@@41)) ($IsBox bx2@@7 t2@@22)) ($Is f@@46 (Tclass._System.___hFunc3 t0@@65 t1@@41 t2@@22 t3@@7)))) (forall ((o@@77 T@U) (fld@@22 T@U) ) (! (let ((a@@104 (FieldTypeInv0 (type fld@@22))))
 (=> (and (and (= (type o@@77) refType) (= (type fld@@22) (FieldType a@@104))) (and (not (= o@@77 null)) (U_2_bool (MapType0Select (Reads3 t0@@65 t1@@41 t2@@22 t3@@7 h1@@23 f@@46 bx0@@39 bx1@@23 bx2@@7) ($Box o@@77))))) (= (MapType1Select (MapType0Select h0@@23 o@@77) fld@@22) (MapType1Select (MapType0Select h1@@23 o@@77) fld@@22))))
 :qid |unknown.0:0|
 :skolemid |828|
 :no-pattern (type o@@77)
 :no-pattern (type fld@@22)
 :no-pattern (U_2_int o@@77)
 :no-pattern (U_2_bool o@@77)
 :no-pattern (U_2_int fld@@22)
 :no-pattern (U_2_bool fld@@22)
)))) (= (Apply3 t0@@65 t1@@41 t2@@22 t3@@7 h0@@23 f@@46 bx0@@39 bx1@@23 bx2@@7) (Apply3 t0@@65 t1@@41 t2@@22 t3@@7 h1@@23 f@@46 bx0@@39 bx1@@23 bx2@@7)))
 :qid |unknown.0:0|
 :skolemid |829|
 :pattern ( ($HeapSucc h0@@23 h1@@23) (Apply3 t0@@65 t1@@41 t2@@22 t3@@7 h1@@23 f@@46 bx0@@39 bx1@@23 bx2@@7))
)))
(assert (forall ((t0@@66 T@U) (t1@@42 T@U) (t2@@23 T@U) (t3@@8 T@U) (heap@@19 T@U) (f@@47 T@U) (bx0@@40 T@U) (bx1@@24 T@U) (bx2@@8 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@66) TyType) (= (type t1@@42) TyType)) (= (type t2@@23) TyType)) (= (type t3@@8) TyType)) (= (type heap@@19) (MapType0Type refType MapType1Type))) (= (type f@@47) HandleTypeType)) (= (type bx0@@40) BoxType)) (= (type bx1@@24) BoxType)) (= (type bx2@@8) BoxType)) (and ($IsGoodHeap heap@@19) (and (and (and ($IsBox bx0@@40 t0@@66) ($IsBox bx1@@24 t1@@42)) ($IsBox bx2@@8 t2@@23)) ($Is f@@47 (Tclass._System.___hFunc3 t0@@66 t1@@42 t2@@23 t3@@8))))) (and (=> (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 $OneHeap f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 heap@@19 f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 heap@@19 f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 $OneHeap f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |830|
 :pattern ( (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 $OneHeap f@@47 bx0@@40 bx1@@24 bx2@@8) ($IsGoodHeap heap@@19))
 :pattern ( (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 heap@@19 f@@47 bx0@@40 bx1@@24 bx2@@8))
)))
(assert (forall ((t0@@67 T@U) (t1@@43 T@U) (t2@@24 T@U) (t3@@9 T@U) (heap@@20 T@U) (f@@48 T@U) (bx0@@41 T@U) (bx1@@25 T@U) (bx2@@9 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@67) TyType) (= (type t1@@43) TyType)) (= (type t2@@24) TyType)) (= (type t3@@9) TyType)) (= (type heap@@20) (MapType0Type refType MapType1Type))) (= (type f@@48) HandleTypeType)) (= (type bx0@@41) BoxType)) (= (type bx1@@25) BoxType)) (= (type bx2@@9) BoxType)) (and (and ($IsGoodHeap heap@@20) (and (and (and ($IsBox bx0@@41 t0@@67) ($IsBox bx1@@25 t1@@43)) ($IsBox bx2@@9 t2@@24)) ($Is f@@48 (Tclass._System.___hFunc3 t0@@67 t1@@43 t2@@24 t3@@9)))) (|Set#Equal| (Reads3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9) (|Set#Empty| BoxType)))) (and (=> (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9) (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 heap@@20 f@@48 bx0@@41 bx1@@25 bx2@@9)) (=> (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 heap@@20 f@@48 bx0@@41 bx1@@25 bx2@@9) (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9))))
 :qid |unknown.0:0|
 :skolemid |831|
 :pattern ( (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9) ($IsGoodHeap heap@@20))
 :pattern ( (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 heap@@20 f@@48 bx0@@41 bx1@@25 bx2@@9))
)))
(assert (forall ((f@@49 T@U) (t0@@68 T@U) (t1@@44 T@U) (t2@@25 T@U) (t3@@10 T@U) ) (!  (=> (and (and (and (and (= (type f@@49) HandleTypeType) (= (type t0@@68) TyType)) (= (type t1@@44) TyType)) (= (type t2@@25) TyType)) (= (type t3@@10) TyType)) (and (=> ($Is f@@49 (Tclass._System.___hFunc3 t0@@68 t1@@44 t2@@25 t3@@10)) (forall ((h@@44 T@U) (bx0@@42 T@U) (bx1@@26 T@U) (bx2@@10 T@U) ) (!  (=> (and (and (and (and (= (type h@@44) (MapType0Type refType MapType1Type)) (= (type bx0@@42) BoxType)) (= (type bx1@@26) BoxType)) (= (type bx2@@10) BoxType)) (and (and ($IsGoodHeap h@@44) (and (and ($IsBox bx0@@42 t0@@68) ($IsBox bx1@@26 t1@@44)) ($IsBox bx2@@10 t2@@25))) (Requires3 t0@@68 t1@@44 t2@@25 t3@@10 h@@44 f@@49 bx0@@42 bx1@@26 bx2@@10))) ($IsBox (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@44 f@@49 bx0@@42 bx1@@26 bx2@@10) t3@@10))
 :qid |DafnyPre.515:12|
 :skolemid |832|
 :pattern ( (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@44 f@@49 bx0@@42 bx1@@26 bx2@@10))
))) (=> (forall ((h@@45 T@U) (bx0@@43 T@U) (bx1@@27 T@U) (bx2@@11 T@U) ) (!  (=> (and (and (and (and (= (type h@@45) (MapType0Type refType MapType1Type)) (= (type bx0@@43) BoxType)) (= (type bx1@@27) BoxType)) (= (type bx2@@11) BoxType)) (and (and ($IsGoodHeap h@@45) (and (and ($IsBox bx0@@43 t0@@68) ($IsBox bx1@@27 t1@@44)) ($IsBox bx2@@11 t2@@25))) (Requires3 t0@@68 t1@@44 t2@@25 t3@@10 h@@45 f@@49 bx0@@43 bx1@@27 bx2@@11))) ($IsBox (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@45 f@@49 bx0@@43 bx1@@27 bx2@@11) t3@@10))
 :qid |DafnyPre.515:12|
 :skolemid |832|
 :pattern ( (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@45 f@@49 bx0@@43 bx1@@27 bx2@@11))
)) ($Is f@@49 (Tclass._System.___hFunc3 t0@@68 t1@@44 t2@@25 t3@@10)))))
 :qid |unknown.0:0|
 :skolemid |833|
 :pattern ( ($Is f@@49 (Tclass._System.___hFunc3 t0@@68 t1@@44 t2@@25 t3@@10)))
)))
(assert (forall ((f@@50 T@U) (t0@@69 T@U) (t1@@45 T@U) (t2@@26 T@U) (t3@@11 T@U) (u0@@2 T@U) (u1@@1 T@U) (u2@@0 T@U) (u3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type f@@50) HandleTypeType) (= (type t0@@69) TyType)) (= (type t1@@45) TyType)) (= (type t2@@26) TyType)) (= (type t3@@11) TyType)) (= (type u0@@2) TyType)) (= (type u1@@1) TyType)) (= (type u2@@0) TyType)) (= (type u3) TyType)) (and (and (and (and ($Is f@@50 (Tclass._System.___hFunc3 t0@@69 t1@@45 t2@@26 t3@@11)) (forall ((bx@@60 T@U) ) (!  (=> (and (= (type bx@@60) BoxType) ($IsBox bx@@60 u0@@2)) ($IsBox bx@@60 t0@@69))
 :qid |unknown.0:0|
 :skolemid |834|
 :pattern ( ($IsBox bx@@60 u0@@2))
 :pattern ( ($IsBox bx@@60 t0@@69))
))) (forall ((bx@@61 T@U) ) (!  (=> (and (= (type bx@@61) BoxType) ($IsBox bx@@61 u1@@1)) ($IsBox bx@@61 t1@@45))
 :qid |unknown.0:0|
 :skolemid |835|
 :pattern ( ($IsBox bx@@61 u1@@1))
 :pattern ( ($IsBox bx@@61 t1@@45))
))) (forall ((bx@@62 T@U) ) (!  (=> (and (= (type bx@@62) BoxType) ($IsBox bx@@62 u2@@0)) ($IsBox bx@@62 t2@@26))
 :qid |unknown.0:0|
 :skolemid |836|
 :pattern ( ($IsBox bx@@62 u2@@0))
 :pattern ( ($IsBox bx@@62 t2@@26))
))) (forall ((bx@@63 T@U) ) (!  (=> (and (= (type bx@@63) BoxType) ($IsBox bx@@63 t3@@11)) ($IsBox bx@@63 u3))
 :qid |unknown.0:0|
 :skolemid |837|
 :pattern ( ($IsBox bx@@63 t3@@11))
 :pattern ( ($IsBox bx@@63 u3))
)))) ($Is f@@50 (Tclass._System.___hFunc3 u0@@2 u1@@1 u2@@0 u3)))
 :qid |unknown.0:0|
 :skolemid |838|
 :pattern ( ($Is f@@50 (Tclass._System.___hFunc3 t0@@69 t1@@45 t2@@26 t3@@11)) ($Is f@@50 (Tclass._System.___hFunc3 u0@@2 u1@@1 u2@@0 u3)))
)))
(assert (forall ((f@@51 T@U) (t0@@70 T@U) (t1@@46 T@U) (t2@@27 T@U) (t3@@12 T@U) (h@@46 T@U) ) (!  (=> (and (and (and (and (and (and (= (type f@@51) HandleTypeType) (= (type t0@@70) TyType)) (= (type t1@@46) TyType)) (= (type t2@@27) TyType)) (= (type t3@@12) TyType)) (= (type h@@46) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@46)) (and (=> ($IsAlloc f@@51 (Tclass._System.___hFunc3 t0@@70 t1@@46 t2@@27 t3@@12) h@@46) (forall ((bx0@@44 T@U) (bx1@@28 T@U) (bx2@@12 T@U) ) (!  (=> (and (and (= (type bx0@@44) BoxType) (= (type bx1@@28) BoxType)) (= (type bx2@@12) BoxType)) (=> (and (and (and (and ($IsBox bx0@@44 t0@@70) ($IsAllocBox bx0@@44 t0@@70 h@@46)) (and ($IsBox bx1@@28 t1@@46) ($IsAllocBox bx1@@28 t1@@46 h@@46))) (and ($IsBox bx2@@12 t2@@27) ($IsAllocBox bx2@@12 t2@@27 h@@46))) (Requires3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12)) (forall ((r@@24 T@U) ) (!  (=> (= (type r@@24) refType) (=> (and (not (= r@@24 null)) (U_2_bool (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12) ($Box r@@24)))) (U_2_bool (MapType1Select (MapType0Select h@@46 r@@24) alloc))))
 :qid |unknown.0:0|
 :skolemid |839|
 :pattern ( (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12) ($Box r@@24)))
))))
 :qid |unknown.0:0|
 :skolemid |840|
 :pattern ( (Apply3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12))
 :pattern ( (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12))
))) (=> (forall ((bx0@@45 T@U) (bx1@@29 T@U) (bx2@@13 T@U) ) (!  (=> (and (and (= (type bx0@@45) BoxType) (= (type bx1@@29) BoxType)) (= (type bx2@@13) BoxType)) (=> (and (and (and (and ($IsBox bx0@@45 t0@@70) ($IsAllocBox bx0@@45 t0@@70 h@@46)) (and ($IsBox bx1@@29 t1@@46) ($IsAllocBox bx1@@29 t1@@46 h@@46))) (and ($IsBox bx2@@13 t2@@27) ($IsAllocBox bx2@@13 t2@@27 h@@46))) (Requires3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13)) (forall ((r@@25 T@U) ) (!  (=> (= (type r@@25) refType) (=> (and (not (= r@@25 null)) (U_2_bool (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13) ($Box r@@25)))) (U_2_bool (MapType1Select (MapType0Select h@@46 r@@25) alloc))))
 :qid |unknown.0:0|
 :skolemid |839|
 :pattern ( (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13) ($Box r@@25)))
))))
 :qid |unknown.0:0|
 :skolemid |840|
 :pattern ( (Apply3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13))
 :pattern ( (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13))
)) ($IsAlloc f@@51 (Tclass._System.___hFunc3 t0@@70 t1@@46 t2@@27 t3@@12) h@@46))))
 :qid |unknown.0:0|
 :skolemid |841|
 :pattern ( ($IsAlloc f@@51 (Tclass._System.___hFunc3 t0@@70 t1@@46 t2@@27 t3@@12) h@@46))
)))
(assert (forall ((f@@52 T@U) (t0@@71 T@U) (t1@@47 T@U) (t2@@28 T@U) (t3@@13 T@U) (h@@47 T@U) ) (!  (=> (and (and (and (and (and (and (= (type f@@52) HandleTypeType) (= (type t0@@71) TyType)) (= (type t1@@47) TyType)) (= (type t2@@28) TyType)) (= (type t3@@13) TyType)) (= (type h@@47) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@47) ($IsAlloc f@@52 (Tclass._System.___hFunc3 t0@@71 t1@@47 t2@@28 t3@@13) h@@47))) (forall ((bx0@@46 T@U) (bx1@@30 T@U) (bx2@@14 T@U) ) (!  (=> (and (and (= (type bx0@@46) BoxType) (= (type bx1@@30) BoxType)) (= (type bx2@@14) BoxType)) (=> (and (and (and ($IsAllocBox bx0@@46 t0@@71 h@@47) ($IsAllocBox bx1@@30 t1@@47 h@@47)) ($IsAllocBox bx2@@14 t2@@28 h@@47)) (Requires3 t0@@71 t1@@47 t2@@28 t3@@13 h@@47 f@@52 bx0@@46 bx1@@30 bx2@@14)) ($IsAllocBox (Apply3 t0@@71 t1@@47 t2@@28 t3@@13 h@@47 f@@52 bx0@@46 bx1@@30 bx2@@14) t3@@13 h@@47)))
 :qid |unknown.0:0|
 :skolemid |842|
 :pattern ( (Apply3 t0@@71 t1@@47 t2@@28 t3@@13 h@@47 f@@52 bx0@@46 bx1@@30 bx2@@14))
)))
 :qid |unknown.0:0|
 :skolemid |843|
 :pattern ( ($IsAlloc f@@52 (Tclass._System.___hFunc3 t0@@71 t1@@47 t2@@28 t3@@13) h@@47))
)))
(assert (forall ((arg0@@181 T@U) (arg1@@88 T@U) (arg2@@44 T@U) (arg3@@23 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3 arg0@@181 arg1@@88 arg2@@44 arg3@@23)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3|
 :pattern ( (Tclass._System.___hPartialFunc3 arg0@@181 arg1@@88 arg2@@44 arg3@@23))
)))
(assert (forall ((|#$T0@@49| T@U) (|#$T1@@33| T@U) (|#$T2@@5| T@U) (|#$R@@53| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@49|) TyType) (= (type |#$T1@@33|) TyType)) (= (type |#$T2@@5|) TyType)) (= (type |#$R@@53|) TyType)) (= (Tag (Tclass._System.___hPartialFunc3 |#$T0@@49| |#$T1@@33| |#$T2@@5| |#$R@@53|)) Tagclass._System.___hPartialFunc3))
 :qid |unknown.0:0|
 :skolemid |844|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@49| |#$T1@@33| |#$T2@@5| |#$R@@53|))
)))
(assert (forall ((arg0@@182 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_0 arg0@@182)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_0|
 :pattern ( (Tclass._System.___hPartialFunc3_0 arg0@@182))
)))
(assert (forall ((|#$T0@@50| T@U) (|#$T1@@34| T@U) (|#$T2@@6| T@U) (|#$R@@54| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@50|) TyType) (= (type |#$T1@@34|) TyType)) (= (type |#$T2@@6|) TyType)) (= (type |#$R@@54|) TyType)) (= (Tclass._System.___hPartialFunc3_0 (Tclass._System.___hPartialFunc3 |#$T0@@50| |#$T1@@34| |#$T2@@6| |#$R@@54|)) |#$T0@@50|))
 :qid |unknown.0:0|
 :skolemid |845|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@50| |#$T1@@34| |#$T2@@6| |#$R@@54|))
)))
(assert (forall ((arg0@@183 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_1 arg0@@183)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_1|
 :pattern ( (Tclass._System.___hPartialFunc3_1 arg0@@183))
)))
(assert (forall ((|#$T0@@51| T@U) (|#$T1@@35| T@U) (|#$T2@@7| T@U) (|#$R@@55| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@51|) TyType) (= (type |#$T1@@35|) TyType)) (= (type |#$T2@@7|) TyType)) (= (type |#$R@@55|) TyType)) (= (Tclass._System.___hPartialFunc3_1 (Tclass._System.___hPartialFunc3 |#$T0@@51| |#$T1@@35| |#$T2@@7| |#$R@@55|)) |#$T1@@35|))
 :qid |unknown.0:0|
 :skolemid |846|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@51| |#$T1@@35| |#$T2@@7| |#$R@@55|))
)))
(assert (forall ((arg0@@184 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_2 arg0@@184)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_2|
 :pattern ( (Tclass._System.___hPartialFunc3_2 arg0@@184))
)))
(assert (forall ((|#$T0@@52| T@U) (|#$T1@@36| T@U) (|#$T2@@8| T@U) (|#$R@@56| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@52|) TyType) (= (type |#$T1@@36|) TyType)) (= (type |#$T2@@8|) TyType)) (= (type |#$R@@56|) TyType)) (= (Tclass._System.___hPartialFunc3_2 (Tclass._System.___hPartialFunc3 |#$T0@@52| |#$T1@@36| |#$T2@@8| |#$R@@56|)) |#$T2@@8|))
 :qid |unknown.0:0|
 :skolemid |847|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@52| |#$T1@@36| |#$T2@@8| |#$R@@56|))
)))
(assert (forall ((arg0@@185 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_3 arg0@@185)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_3|
 :pattern ( (Tclass._System.___hPartialFunc3_3 arg0@@185))
)))
(assert (forall ((|#$T0@@53| T@U) (|#$T1@@37| T@U) (|#$T2@@9| T@U) (|#$R@@57| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@53|) TyType) (= (type |#$T1@@37|) TyType)) (= (type |#$T2@@9|) TyType)) (= (type |#$R@@57|) TyType)) (= (Tclass._System.___hPartialFunc3_3 (Tclass._System.___hPartialFunc3 |#$T0@@53| |#$T1@@37| |#$T2@@9| |#$R@@57|)) |#$R@@57|))
 :qid |unknown.0:0|
 :skolemid |848|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@53| |#$T1@@37| |#$T2@@9| |#$R@@57|))
)))
(assert (forall ((|#$T0@@54| T@U) (|#$T1@@38| T@U) (|#$T2@@10| T@U) (|#$R@@58| T@U) (bx@@64 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@54|) TyType) (= (type |#$T1@@38|) TyType)) (= (type |#$T2@@10|) TyType)) (= (type |#$R@@58|) TyType)) (= (type bx@@64) BoxType)) ($IsBox bx@@64 (Tclass._System.___hPartialFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@10| |#$R@@58|))) (and (= ($Box ($Unbox HandleTypeType bx@@64)) bx@@64) ($Is ($Unbox HandleTypeType bx@@64) (Tclass._System.___hPartialFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@10| |#$R@@58|))))
 :qid |unknown.0:0|
 :skolemid |849|
 :pattern ( ($IsBox bx@@64 (Tclass._System.___hPartialFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@10| |#$R@@58|)))
)))
(assert (forall ((|#$T0@@55| T@U) (|#$T1@@39| T@U) (|#$T2@@11| T@U) (|#$R@@59| T@U) (|f#0@@11| T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@55|) TyType) (= (type |#$T1@@39|) TyType)) (= (type |#$T2@@11|) TyType)) (= (type |#$R@@59|) TyType)) (= (type |f#0@@11|) HandleTypeType)) (and (=> ($Is |f#0@@11| (Tclass._System.___hPartialFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@11| |#$R@@59|)) (and ($Is |f#0@@11| (Tclass._System.___hFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@11| |#$R@@59|)) (forall ((|x0#0@@7| T@U) (|x1#0@@3| T@U) (|x2#0| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@7|) BoxType) (= (type |x1#0@@3|) BoxType)) (= (type |x2#0|) BoxType)) (and (and ($IsBox |x0#0@@7| |#$T0@@55|) ($IsBox |x1#0@@3| |#$T1@@39|)) ($IsBox |x2#0| |#$T2@@11|))) (|Set#Equal| (Reads3 |#$T0@@55| |#$T1@@39| |#$T2@@11| |#$R@@59| $OneHeap |f#0@@11| |x0#0@@7| |x1#0@@3| |x2#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |850|
 :no-pattern (type |x0#0@@7|)
 :no-pattern (type |x1#0@@3|)
 :no-pattern (type |x2#0|)
 :no-pattern (U_2_int |x0#0@@7|)
 :no-pattern (U_2_bool |x0#0@@7|)
 :no-pattern (U_2_int |x1#0@@3|)
 :no-pattern (U_2_bool |x1#0@@3|)
 :no-pattern (U_2_int |x2#0|)
 :no-pattern (U_2_bool |x2#0|)
)))) (=> (and ($Is |f#0@@11| (Tclass._System.___hFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@11| |#$R@@59|)) (forall ((|x0#0@@8| T@U) (|x1#0@@4| T@U) (|x2#0@@0| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@8|) BoxType) (= (type |x1#0@@4|) BoxType)) (= (type |x2#0@@0|) BoxType)) (and (and ($IsBox |x0#0@@8| |#$T0@@55|) ($IsBox |x1#0@@4| |#$T1@@39|)) ($IsBox |x2#0@@0| |#$T2@@11|))) (|Set#Equal| (Reads3 |#$T0@@55| |#$T1@@39| |#$T2@@11| |#$R@@59| $OneHeap |f#0@@11| |x0#0@@8| |x1#0@@4| |x2#0@@0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |850|
 :no-pattern (type |x0#0@@8|)
 :no-pattern (type |x1#0@@4|)
 :no-pattern (type |x2#0@@0|)
 :no-pattern (U_2_int |x0#0@@8|)
 :no-pattern (U_2_bool |x0#0@@8|)
 :no-pattern (U_2_int |x1#0@@4|)
 :no-pattern (U_2_bool |x1#0@@4|)
 :no-pattern (U_2_int |x2#0@@0|)
 :no-pattern (U_2_bool |x2#0@@0|)
))) ($Is |f#0@@11| (Tclass._System.___hPartialFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@11| |#$R@@59|)))))
 :qid |unknown.0:0|
 :skolemid |851|
 :pattern ( ($Is |f#0@@11| (Tclass._System.___hPartialFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@11| |#$R@@59|)))
)))
(assert (forall ((|#$T0@@56| T@U) (|#$T1@@40| T@U) (|#$T2@@12| T@U) (|#$R@@60| T@U) (|f#0@@12| T@U) ($h@@16 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@56|) TyType) (= (type |#$T1@@40|) TyType)) (= (type |#$T2@@12|) TyType)) (= (type |#$R@@60|) TyType)) (= (type |f#0@@12|) HandleTypeType)) (= (type $h@@16) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@12| (Tclass._System.___hPartialFunc3 |#$T0@@56| |#$T1@@40| |#$T2@@12| |#$R@@60|) $h@@16) ($IsAlloc |f#0@@12| (Tclass._System.___hFunc3 |#$T0@@56| |#$T1@@40| |#$T2@@12| |#$R@@60|) $h@@16)) (=> ($IsAlloc |f#0@@12| (Tclass._System.___hFunc3 |#$T0@@56| |#$T1@@40| |#$T2@@12| |#$R@@60|) $h@@16) ($IsAlloc |f#0@@12| (Tclass._System.___hPartialFunc3 |#$T0@@56| |#$T1@@40| |#$T2@@12| |#$R@@60|) $h@@16))))
 :qid |unknown.0:0|
 :skolemid |852|
 :pattern ( ($IsAlloc |f#0@@12| (Tclass._System.___hPartialFunc3 |#$T0@@56| |#$T1@@40| |#$T2@@12| |#$R@@60|) $h@@16))
)))
(assert (forall ((arg0@@186 T@U) (arg1@@89 T@U) (arg2@@45 T@U) (arg3@@24 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3 arg0@@186 arg1@@89 arg2@@45 arg3@@24)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3|
 :pattern ( (Tclass._System.___hTotalFunc3 arg0@@186 arg1@@89 arg2@@45 arg3@@24))
)))
(assert (forall ((|#$T0@@57| T@U) (|#$T1@@41| T@U) (|#$T2@@13| T@U) (|#$R@@61| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@57|) TyType) (= (type |#$T1@@41|) TyType)) (= (type |#$T2@@13|) TyType)) (= (type |#$R@@61|) TyType)) (= (Tag (Tclass._System.___hTotalFunc3 |#$T0@@57| |#$T1@@41| |#$T2@@13| |#$R@@61|)) Tagclass._System.___hTotalFunc3))
 :qid |unknown.0:0|
 :skolemid |853|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@57| |#$T1@@41| |#$T2@@13| |#$R@@61|))
)))
(assert (forall ((arg0@@187 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_0 arg0@@187)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_0|
 :pattern ( (Tclass._System.___hTotalFunc3_0 arg0@@187))
)))
(assert (forall ((|#$T0@@58| T@U) (|#$T1@@42| T@U) (|#$T2@@14| T@U) (|#$R@@62| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@58|) TyType) (= (type |#$T1@@42|) TyType)) (= (type |#$T2@@14|) TyType)) (= (type |#$R@@62|) TyType)) (= (Tclass._System.___hTotalFunc3_0 (Tclass._System.___hTotalFunc3 |#$T0@@58| |#$T1@@42| |#$T2@@14| |#$R@@62|)) |#$T0@@58|))
 :qid |unknown.0:0|
 :skolemid |854|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@58| |#$T1@@42| |#$T2@@14| |#$R@@62|))
)))
(assert (forall ((arg0@@188 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_1 arg0@@188)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_1|
 :pattern ( (Tclass._System.___hTotalFunc3_1 arg0@@188))
)))
(assert (forall ((|#$T0@@59| T@U) (|#$T1@@43| T@U) (|#$T2@@15| T@U) (|#$R@@63| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@59|) TyType) (= (type |#$T1@@43|) TyType)) (= (type |#$T2@@15|) TyType)) (= (type |#$R@@63|) TyType)) (= (Tclass._System.___hTotalFunc3_1 (Tclass._System.___hTotalFunc3 |#$T0@@59| |#$T1@@43| |#$T2@@15| |#$R@@63|)) |#$T1@@43|))
 :qid |unknown.0:0|
 :skolemid |855|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@59| |#$T1@@43| |#$T2@@15| |#$R@@63|))
)))
(assert (forall ((arg0@@189 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_2 arg0@@189)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_2|
 :pattern ( (Tclass._System.___hTotalFunc3_2 arg0@@189))
)))
(assert (forall ((|#$T0@@60| T@U) (|#$T1@@44| T@U) (|#$T2@@16| T@U) (|#$R@@64| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@60|) TyType) (= (type |#$T1@@44|) TyType)) (= (type |#$T2@@16|) TyType)) (= (type |#$R@@64|) TyType)) (= (Tclass._System.___hTotalFunc3_2 (Tclass._System.___hTotalFunc3 |#$T0@@60| |#$T1@@44| |#$T2@@16| |#$R@@64|)) |#$T2@@16|))
 :qid |unknown.0:0|
 :skolemid |856|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@60| |#$T1@@44| |#$T2@@16| |#$R@@64|))
)))
(assert (forall ((arg0@@190 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_3 arg0@@190)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_3|
 :pattern ( (Tclass._System.___hTotalFunc3_3 arg0@@190))
)))
(assert (forall ((|#$T0@@61| T@U) (|#$T1@@45| T@U) (|#$T2@@17| T@U) (|#$R@@65| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@61|) TyType) (= (type |#$T1@@45|) TyType)) (= (type |#$T2@@17|) TyType)) (= (type |#$R@@65|) TyType)) (= (Tclass._System.___hTotalFunc3_3 (Tclass._System.___hTotalFunc3 |#$T0@@61| |#$T1@@45| |#$T2@@17| |#$R@@65|)) |#$R@@65|))
 :qid |unknown.0:0|
 :skolemid |857|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@61| |#$T1@@45| |#$T2@@17| |#$R@@65|))
)))
(assert (forall ((|#$T0@@62| T@U) (|#$T1@@46| T@U) (|#$T2@@18| T@U) (|#$R@@66| T@U) (bx@@65 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@62|) TyType) (= (type |#$T1@@46|) TyType)) (= (type |#$T2@@18|) TyType)) (= (type |#$R@@66|) TyType)) (= (type bx@@65) BoxType)) ($IsBox bx@@65 (Tclass._System.___hTotalFunc3 |#$T0@@62| |#$T1@@46| |#$T2@@18| |#$R@@66|))) (and (= ($Box ($Unbox HandleTypeType bx@@65)) bx@@65) ($Is ($Unbox HandleTypeType bx@@65) (Tclass._System.___hTotalFunc3 |#$T0@@62| |#$T1@@46| |#$T2@@18| |#$R@@66|))))
 :qid |unknown.0:0|
 :skolemid |858|
 :pattern ( ($IsBox bx@@65 (Tclass._System.___hTotalFunc3 |#$T0@@62| |#$T1@@46| |#$T2@@18| |#$R@@66|)))
)))
(assert (forall ((|#$T0@@63| T@U) (|#$T1@@47| T@U) (|#$T2@@19| T@U) (|#$R@@67| T@U) (|f#0@@13| T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@63|) TyType) (= (type |#$T1@@47|) TyType)) (= (type |#$T2@@19|) TyType)) (= (type |#$R@@67|) TyType)) (= (type |f#0@@13|) HandleTypeType)) (and (=> ($Is |f#0@@13| (Tclass._System.___hTotalFunc3 |#$T0@@63| |#$T1@@47| |#$T2@@19| |#$R@@67|)) (and ($Is |f#0@@13| (Tclass._System.___hPartialFunc3 |#$T0@@63| |#$T1@@47| |#$T2@@19| |#$R@@67|)) (forall ((|x0#0@@9| T@U) (|x1#0@@5| T@U) (|x2#0@@1| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@9|) BoxType) (= (type |x1#0@@5|) BoxType)) (= (type |x2#0@@1|) BoxType)) (and (and ($IsBox |x0#0@@9| |#$T0@@63|) ($IsBox |x1#0@@5| |#$T1@@47|)) ($IsBox |x2#0@@1| |#$T2@@19|))) (Requires3 |#$T0@@63| |#$T1@@47| |#$T2@@19| |#$R@@67| $OneHeap |f#0@@13| |x0#0@@9| |x1#0@@5| |x2#0@@1|))
 :qid |unknown.0:0|
 :skolemid |859|
 :no-pattern (type |x0#0@@9|)
 :no-pattern (type |x1#0@@5|)
 :no-pattern (type |x2#0@@1|)
 :no-pattern (U_2_int |x0#0@@9|)
 :no-pattern (U_2_bool |x0#0@@9|)
 :no-pattern (U_2_int |x1#0@@5|)
 :no-pattern (U_2_bool |x1#0@@5|)
 :no-pattern (U_2_int |x2#0@@1|)
 :no-pattern (U_2_bool |x2#0@@1|)
)))) (=> (and ($Is |f#0@@13| (Tclass._System.___hPartialFunc3 |#$T0@@63| |#$T1@@47| |#$T2@@19| |#$R@@67|)) (forall ((|x0#0@@10| T@U) (|x1#0@@6| T@U) (|x2#0@@2| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@10|) BoxType) (= (type |x1#0@@6|) BoxType)) (= (type |x2#0@@2|) BoxType)) (and (and ($IsBox |x0#0@@10| |#$T0@@63|) ($IsBox |x1#0@@6| |#$T1@@47|)) ($IsBox |x2#0@@2| |#$T2@@19|))) (Requires3 |#$T0@@63| |#$T1@@47| |#$T2@@19| |#$R@@67| $OneHeap |f#0@@13| |x0#0@@10| |x1#0@@6| |x2#0@@2|))
 :qid |unknown.0:0|
 :skolemid |859|
 :no-pattern (type |x0#0@@10|)
 :no-pattern (type |x1#0@@6|)
 :no-pattern (type |x2#0@@2|)
 :no-pattern (U_2_int |x0#0@@10|)
 :no-pattern (U_2_bool |x0#0@@10|)
 :no-pattern (U_2_int |x1#0@@6|)
 :no-pattern (U_2_bool |x1#0@@6|)
 :no-pattern (U_2_int |x2#0@@2|)
 :no-pattern (U_2_bool |x2#0@@2|)
))) ($Is |f#0@@13| (Tclass._System.___hTotalFunc3 |#$T0@@63| |#$T1@@47| |#$T2@@19| |#$R@@67|)))))
 :qid |unknown.0:0|
 :skolemid |860|
 :pattern ( ($Is |f#0@@13| (Tclass._System.___hTotalFunc3 |#$T0@@63| |#$T1@@47| |#$T2@@19| |#$R@@67|)))
)))
(assert (forall ((|#$T0@@64| T@U) (|#$T1@@48| T@U) (|#$T2@@20| T@U) (|#$R@@68| T@U) (|f#0@@14| T@U) ($h@@17 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@64|) TyType) (= (type |#$T1@@48|) TyType)) (= (type |#$T2@@20|) TyType)) (= (type |#$R@@68|) TyType)) (= (type |f#0@@14|) HandleTypeType)) (= (type $h@@17) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@14| (Tclass._System.___hTotalFunc3 |#$T0@@64| |#$T1@@48| |#$T2@@20| |#$R@@68|) $h@@17) ($IsAlloc |f#0@@14| (Tclass._System.___hPartialFunc3 |#$T0@@64| |#$T1@@48| |#$T2@@20| |#$R@@68|) $h@@17)) (=> ($IsAlloc |f#0@@14| (Tclass._System.___hPartialFunc3 |#$T0@@64| |#$T1@@48| |#$T2@@20| |#$R@@68|) $h@@17) ($IsAlloc |f#0@@14| (Tclass._System.___hTotalFunc3 |#$T0@@64| |#$T1@@48| |#$T2@@20| |#$R@@68|) $h@@17))))
 :qid |unknown.0:0|
 :skolemid |861|
 :pattern ( ($IsAlloc |f#0@@14| (Tclass._System.___hTotalFunc3 |#$T0@@64| |#$T1@@48| |#$T2@@20| |#$R@@68|) $h@@17))
)))
(assert (= (type |#_System._tuple#0._#Make0|) DatatypeTypeType))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (forall ((d@@6 T@U) ) (!  (=> (= (type d@@6) DatatypeTypeType) (and (=> (_System.Tuple0.___hMake0_q d@@6) (= (DatatypeCtorId d@@6) |##_System._tuple#0._#Make0|)) (=> (= (DatatypeCtorId d@@6) |##_System._tuple#0._#Make0|) (_System.Tuple0.___hMake0_q d@@6))))
 :qid |unknown.0:0|
 :skolemid |862|
 :pattern ( (_System.Tuple0.___hMake0_q d@@6))
)))
(assert (forall ((d@@7 T@U) ) (!  (=> (and (= (type d@@7) DatatypeTypeType) (_System.Tuple0.___hMake0_q d@@7)) (= d@@7 |#_System._tuple#0._#Make0|))
 :qid |unknown.0:0|
 :skolemid |863|
 :pattern ( (_System.Tuple0.___hMake0_q d@@7))
)))
(assert (= (type Tclass._System.Tuple0) TyType))
(assert (= (Tag Tclass._System.Tuple0) Tagclass._System.Tuple0))
(assert (forall ((bx@@66 T@U) ) (!  (=> (and (= (type bx@@66) BoxType) ($IsBox bx@@66 Tclass._System.Tuple0)) (and (= ($Box ($Unbox DatatypeTypeType bx@@66)) bx@@66) ($Is ($Unbox DatatypeTypeType bx@@66) Tclass._System.Tuple0)))
 :qid |unknown.0:0|
 :skolemid |864|
 :pattern ( ($IsBox bx@@66 Tclass._System.Tuple0))
)))
(assert ($Is |#_System._tuple#0._#Make0| Tclass._System.Tuple0))
(assert (forall (($h@@18 T@U) ) (!  (=> (and (= (type $h@@18) (MapType0Type refType MapType1Type)) ($IsGoodHeap $h@@18)) ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@18))
 :qid |DafnyPre.515:12|
 :skolemid |865|
 :pattern ( ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@18))
)))
(assert (= |#_System._tuple#0._#Make0| (Lit |#_System._tuple#0._#Make0|)))
(assert (forall ((d@@8 T@U) ) (!  (=> (and (= (type d@@8) DatatypeTypeType) (|$IsA#_System.Tuple0| d@@8)) (_System.Tuple0.___hMake0_q d@@8))
 :qid |unknown.0:0|
 :skolemid |866|
 :pattern ( (|$IsA#_System.Tuple0| d@@8))
)))
(assert (forall ((d@@9 T@U) ) (!  (=> (and (= (type d@@9) DatatypeTypeType) ($Is d@@9 Tclass._System.Tuple0)) (_System.Tuple0.___hMake0_q d@@9))
 :qid |unknown.0:0|
 :skolemid |867|
 :pattern ( (_System.Tuple0.___hMake0_q d@@9) ($Is d@@9 Tclass._System.Tuple0))
)))
(assert (forall ((a@@105 T@U) (b@@60 T@U) ) (!  (=> (and (and (= (type a@@105) DatatypeTypeType) (= (type b@@60) DatatypeTypeType)) true) (and (=> (|_System.Tuple0#Equal| a@@105 b@@60) true) (=> true (|_System.Tuple0#Equal| a@@105 b@@60))))
 :qid |unknown.0:0|
 :skolemid |868|
 :pattern ( (|_System.Tuple0#Equal| a@@105 b@@60))
)))
(assert (forall ((a@@106 T@U) (b@@61 T@U) ) (!  (=> (and (= (type a@@106) DatatypeTypeType) (= (type b@@61) DatatypeTypeType)) (and (=> (|_System.Tuple0#Equal| a@@106 b@@61) (= a@@106 b@@61)) (=> (= a@@106 b@@61) (|_System.Tuple0#Equal| a@@106 b@@61))))
 :qid |unknown.0:0|
 :skolemid |869|
 :pattern ( (|_System.Tuple0#Equal| a@@106 b@@61))
)))
(assert (= (type |#_module.List.Nil|) DatatypeTypeType))
(assert (= (DatatypeCtorId |#_module.List.Nil|) |##_module.List.Nil|))
(assert (forall ((d@@10 T@U) ) (!  (=> (= (type d@@10) DatatypeTypeType) (and (=> (_module.List.Nil_q d@@10) (= (DatatypeCtorId d@@10) |##_module.List.Nil|)) (=> (= (DatatypeCtorId d@@10) |##_module.List.Nil|) (_module.List.Nil_q d@@10))))
 :qid |unknown.0:0|
 :skolemid |870|
 :pattern ( (_module.List.Nil_q d@@10))
)))
(assert (forall ((d@@11 T@U) ) (!  (=> (and (= (type d@@11) DatatypeTypeType) (_module.List.Nil_q d@@11)) (= d@@11 |#_module.List.Nil|))
 :qid |unknown.0:0|
 :skolemid |871|
 :pattern ( (_module.List.Nil_q d@@11))
)))
(assert (forall ((arg0@@191 T@U) ) (! (= (type (Tclass._module.List arg0@@191)) TyType)
 :qid |funType:Tclass._module.List|
 :pattern ( (Tclass._module.List arg0@@191))
)))
(assert (forall ((_module.List$X T@U) ) (!  (=> (= (type _module.List$X) TyType) (= (Tag (Tclass._module.List _module.List$X)) Tagclass._module.List))
 :qid |unknown.0:0|
 :skolemid |872|
 :pattern ( (Tclass._module.List _module.List$X))
)))
(assert (forall ((arg0@@192 T@U) ) (! (= (type (Tclass._module.List_0 arg0@@192)) TyType)
 :qid |funType:Tclass._module.List_0|
 :pattern ( (Tclass._module.List_0 arg0@@192))
)))
(assert (forall ((_module.List$X@@0 T@U) ) (!  (=> (= (type _module.List$X@@0) TyType) (= (Tclass._module.List_0 (Tclass._module.List _module.List$X@@0)) _module.List$X@@0))
 :qid |unknown.0:0|
 :skolemid |873|
 :pattern ( (Tclass._module.List _module.List$X@@0))
)))
(assert (forall ((_module.List$X@@1 T@U) (bx@@67 T@U) ) (!  (=> (and (and (= (type _module.List$X@@1) TyType) (= (type bx@@67) BoxType)) ($IsBox bx@@67 (Tclass._module.List _module.List$X@@1))) (and (= ($Box ($Unbox DatatypeTypeType bx@@67)) bx@@67) ($Is ($Unbox DatatypeTypeType bx@@67) (Tclass._module.List _module.List$X@@1))))
 :qid |unknown.0:0|
 :skolemid |874|
 :pattern ( ($IsBox bx@@67 (Tclass._module.List _module.List$X@@1)))
)))
(assert (forall ((_module.List$X@@2 T@U) ) (!  (=> (= (type _module.List$X@@2) TyType) ($Is |#_module.List.Nil| (Tclass._module.List _module.List$X@@2)))
 :qid |unknown.0:0|
 :skolemid |875|
 :pattern ( ($Is |#_module.List.Nil| (Tclass._module.List _module.List$X@@2)))
)))
(assert (forall ((_module.List$X@@3 T@U) ($h@@19 T@U) ) (!  (=> (and (and (= (type _module.List$X@@3) TyType) (= (type $h@@19) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@19)) ($IsAlloc |#_module.List.Nil| (Tclass._module.List _module.List$X@@3) $h@@19))
 :qid |unknown.0:0|
 :skolemid |876|
 :pattern ( ($IsAlloc |#_module.List.Nil| (Tclass._module.List _module.List$X@@3) $h@@19))
)))
(assert (= |#_module.List.Nil| (Lit |#_module.List.Nil|)))
(assert (forall ((arg0@@193 T@U) (arg1@@90 T@U) ) (! (= (type (|#_module.List.Cons| arg0@@193 arg1@@90)) DatatypeTypeType)
 :qid |funType:#_module.List.Cons|
 :pattern ( (|#_module.List.Cons| arg0@@193 arg1@@90))
)))
(assert (forall ((|a#19#0#0| T@U) (|a#19#1#0| T@U) ) (!  (=> (and (= (type |a#19#0#0|) BoxType) (= (type |a#19#1#0|) DatatypeTypeType)) (= (DatatypeCtorId (|#_module.List.Cons| |a#19#0#0| |a#19#1#0|)) |##_module.List.Cons|))
 :qid |SMNADTLi.4:31|
 :skolemid |877|
 :pattern ( (|#_module.List.Cons| |a#19#0#0| |a#19#1#0|))
)))
(assert (forall ((d@@12 T@U) ) (!  (=> (= (type d@@12) DatatypeTypeType) (and (=> (_module.List.Cons_q d@@12) (= (DatatypeCtorId d@@12) |##_module.List.Cons|)) (=> (= (DatatypeCtorId d@@12) |##_module.List.Cons|) (_module.List.Cons_q d@@12))))
 :qid |unknown.0:0|
 :skolemid |878|
 :pattern ( (_module.List.Cons_q d@@12))
)))
(assert (forall ((d@@13 T@U) ) (!  (=> (and (= (type d@@13) DatatypeTypeType) (_module.List.Cons_q d@@13)) (exists ((|a#20#0#0| T@U) (|a#20#1#0| T@U) ) (!  (and (and (= (type |a#20#0#0|) BoxType) (= (type |a#20#1#0|) DatatypeTypeType)) (= d@@13 (|#_module.List.Cons| |a#20#0#0| |a#20#1#0|)))
 :qid |SMNADTLi.4:31|
 :skolemid |879|
 :no-pattern (type |a#20#0#0|)
 :no-pattern (type |a#20#1#0|)
 :no-pattern (U_2_int |a#20#0#0|)
 :no-pattern (U_2_bool |a#20#0#0|)
 :no-pattern (U_2_int |a#20#1#0|)
 :no-pattern (U_2_bool |a#20#1#0|)
)))
 :qid |unknown.0:0|
 :skolemid |880|
 :pattern ( (_module.List.Cons_q d@@13))
)))
(assert (forall ((_module.List$X@@4 T@U) (|a#21#0#0| T@U) (|a#21#1#0| T@U) ) (!  (=> (and (and (= (type _module.List$X@@4) TyType) (= (type |a#21#0#0|) BoxType)) (= (type |a#21#1#0|) DatatypeTypeType)) (and (=> ($Is (|#_module.List.Cons| |a#21#0#0| |a#21#1#0|) (Tclass._module.List _module.List$X@@4)) (and ($IsBox |a#21#0#0| _module.List$X@@4) ($Is |a#21#1#0| (Tclass._module.List _module.List$X@@4)))) (=> (and ($IsBox |a#21#0#0| _module.List$X@@4) ($Is |a#21#1#0| (Tclass._module.List _module.List$X@@4))) ($Is (|#_module.List.Cons| |a#21#0#0| |a#21#1#0|) (Tclass._module.List _module.List$X@@4)))))
 :qid |unknown.0:0|
 :skolemid |881|
 :pattern ( ($Is (|#_module.List.Cons| |a#21#0#0| |a#21#1#0|) (Tclass._module.List _module.List$X@@4)))
)))
(assert (forall ((_module.List$X@@5 T@U) (|a#22#0#0| T@U) (|a#22#1#0| T@U) ($h@@20 T@U) ) (!  (=> (and (and (and (and (= (type _module.List$X@@5) TyType) (= (type |a#22#0#0|) BoxType)) (= (type |a#22#1#0|) DatatypeTypeType)) (= (type $h@@20) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@20)) (and (=> ($IsAlloc (|#_module.List.Cons| |a#22#0#0| |a#22#1#0|) (Tclass._module.List _module.List$X@@5) $h@@20) (and ($IsAllocBox |a#22#0#0| _module.List$X@@5 $h@@20) ($IsAlloc |a#22#1#0| (Tclass._module.List _module.List$X@@5) $h@@20))) (=> (and ($IsAllocBox |a#22#0#0| _module.List$X@@5 $h@@20) ($IsAlloc |a#22#1#0| (Tclass._module.List _module.List$X@@5) $h@@20)) ($IsAlloc (|#_module.List.Cons| |a#22#0#0| |a#22#1#0|) (Tclass._module.List _module.List$X@@5) $h@@20))))
 :qid |unknown.0:0|
 :skolemid |882|
 :pattern ( ($IsAlloc (|#_module.List.Cons| |a#22#0#0| |a#22#1#0|) (Tclass._module.List _module.List$X@@5) $h@@20))
)))
(assert (forall ((arg0@@194 T@U) ) (! (= (type (_module.List.head arg0@@194)) BoxType)
 :qid |funType:_module.List.head|
 :pattern ( (_module.List.head arg0@@194))
)))
(assert (forall ((d@@14 T@U) (_module.List$X@@6 T@U) ($h@@21 T@U) ) (!  (=> (and (and (and (= (type d@@14) DatatypeTypeType) (= (type _module.List$X@@6) TyType)) (= (type $h@@21) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@21) (and (_module.List.Cons_q d@@14) ($IsAlloc d@@14 (Tclass._module.List _module.List$X@@6) $h@@21)))) ($IsAllocBox (_module.List.head d@@14) _module.List$X@@6 $h@@21))
 :qid |unknown.0:0|
 :skolemid |883|
 :pattern ( ($IsAllocBox (_module.List.head d@@14) _module.List$X@@6 $h@@21))
)))
(assert (forall ((arg0@@195 T@U) ) (! (= (type (_module.List.tail arg0@@195)) DatatypeTypeType)
 :qid |funType:_module.List.tail|
 :pattern ( (_module.List.tail arg0@@195))
)))
(assert (forall ((d@@15 T@U) (_module.List$X@@7 T@U) ($h@@22 T@U) ) (!  (=> (and (and (and (= (type d@@15) DatatypeTypeType) (= (type _module.List$X@@7) TyType)) (= (type $h@@22) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@22) (and (_module.List.Cons_q d@@15) ($IsAlloc d@@15 (Tclass._module.List _module.List$X@@7) $h@@22)))) ($IsAlloc (_module.List.tail d@@15) (Tclass._module.List _module.List$X@@7) $h@@22))
 :qid |unknown.0:0|
 :skolemid |884|
 :pattern ( ($IsAlloc (_module.List.tail d@@15) (Tclass._module.List _module.List$X@@7) $h@@22))
)))
(assert (forall ((|a#23#0#0| T@U) (|a#23#1#0| T@U) ) (!  (=> (and (= (type |a#23#0#0|) BoxType) (= (type |a#23#1#0|) DatatypeTypeType)) (= (|#_module.List.Cons| (Lit |a#23#0#0|) (Lit |a#23#1#0|)) (Lit (|#_module.List.Cons| |a#23#0#0| |a#23#1#0|))))
 :qid |SMNADTLi.4:31|
 :skolemid |885|
 :pattern ( (|#_module.List.Cons| (Lit |a#23#0#0|) (Lit |a#23#1#0|)))
)))
(assert (forall ((|a#24#0#0| T@U) (|a#24#1#0| T@U) ) (!  (=> (and (= (type |a#24#0#0|) BoxType) (= (type |a#24#1#0|) DatatypeTypeType)) (= (_module.List.head (|#_module.List.Cons| |a#24#0#0| |a#24#1#0|)) |a#24#0#0|))
 :qid |SMNADTLi.4:31|
 :skolemid |886|
 :pattern ( (|#_module.List.Cons| |a#24#0#0| |a#24#1#0|))
)))
(assert (forall ((|a#25#0#0| T@U) (|a#25#1#0| T@U) ) (!  (=> (and (= (type |a#25#0#0|) BoxType) (= (type |a#25#1#0|) DatatypeTypeType)) (< (BoxRank |a#25#0#0|) (DtRank (|#_module.List.Cons| |a#25#0#0| |a#25#1#0|))))
 :qid |SMNADTLi.4:31|
 :skolemid |887|
 :pattern ( (|#_module.List.Cons| |a#25#0#0| |a#25#1#0|))
)))
(assert (forall ((|a#26#0#0| T@U) (|a#26#1#0| T@U) ) (!  (=> (and (= (type |a#26#0#0|) BoxType) (= (type |a#26#1#0|) DatatypeTypeType)) (= (_module.List.tail (|#_module.List.Cons| |a#26#0#0| |a#26#1#0|)) |a#26#1#0|))
 :qid |SMNADTLi.4:31|
 :skolemid |888|
 :pattern ( (|#_module.List.Cons| |a#26#0#0| |a#26#1#0|))
)))
(assert (forall ((|a#27#0#0| T@U) (|a#27#1#0| T@U) ) (!  (=> (and (= (type |a#27#0#0|) BoxType) (= (type |a#27#1#0|) DatatypeTypeType)) (< (DtRank |a#27#1#0|) (DtRank (|#_module.List.Cons| |a#27#0#0| |a#27#1#0|))))
 :qid |SMNADTLi.4:31|
 :skolemid |889|
 :pattern ( (|#_module.List.Cons| |a#27#0#0| |a#27#1#0|))
)))
(assert (forall ((d@@16 T@U) ) (!  (=> (and (= (type d@@16) DatatypeTypeType) (|$IsA#_module.List| d@@16)) (or (_module.List.Nil_q d@@16) (_module.List.Cons_q d@@16)))
 :qid |unknown.0:0|
 :skolemid |890|
 :pattern ( (|$IsA#_module.List| d@@16))
)))
(assert (forall ((_module.List$X@@8 T@U) (d@@17 T@U) ) (!  (=> (and (and (= (type _module.List$X@@8) TyType) (= (type d@@17) DatatypeTypeType)) ($Is d@@17 (Tclass._module.List _module.List$X@@8))) (or (_module.List.Nil_q d@@17) (_module.List.Cons_q d@@17)))
 :qid |unknown.0:0|
 :skolemid |891|
 :pattern ( (_module.List.Cons_q d@@17) ($Is d@@17 (Tclass._module.List _module.List$X@@8)))
 :pattern ( (_module.List.Nil_q d@@17) ($Is d@@17 (Tclass._module.List _module.List$X@@8)))
)))
(assert (forall ((a@@107 T@U) (b@@62 T@U) ) (!  (=> (and (and (= (type a@@107) DatatypeTypeType) (= (type b@@62) DatatypeTypeType)) (and (_module.List.Nil_q a@@107) (_module.List.Nil_q b@@62))) (and (=> (|_module.List#Equal| a@@107 b@@62) true) (=> true (|_module.List#Equal| a@@107 b@@62))))
 :qid |unknown.0:0|
 :skolemid |892|
 :pattern ( (|_module.List#Equal| a@@107 b@@62) (_module.List.Nil_q a@@107))
 :pattern ( (|_module.List#Equal| a@@107 b@@62) (_module.List.Nil_q b@@62))
)))
(assert (forall ((a@@108 T@U) (b@@63 T@U) ) (!  (=> (and (and (= (type a@@108) DatatypeTypeType) (= (type b@@63) DatatypeTypeType)) (and (_module.List.Cons_q a@@108) (_module.List.Cons_q b@@63))) (and (=> (|_module.List#Equal| a@@108 b@@63) (and (= (_module.List.head a@@108) (_module.List.head b@@63)) (|_module.List#Equal| (_module.List.tail a@@108) (_module.List.tail b@@63)))) (=> (and (= (_module.List.head a@@108) (_module.List.head b@@63)) (|_module.List#Equal| (_module.List.tail a@@108) (_module.List.tail b@@63))) (|_module.List#Equal| a@@108 b@@63))))
 :qid |unknown.0:0|
 :skolemid |893|
 :pattern ( (|_module.List#Equal| a@@108 b@@63) (_module.List.Cons_q a@@108))
 :pattern ( (|_module.List#Equal| a@@108 b@@63) (_module.List.Cons_q b@@63))
)))
(assert (forall ((a@@109 T@U) (b@@64 T@U) ) (!  (=> (and (= (type a@@109) DatatypeTypeType) (= (type b@@64) DatatypeTypeType)) (and (=> (|_module.List#Equal| a@@109 b@@64) (= a@@109 b@@64)) (=> (= a@@109 b@@64) (|_module.List#Equal| a@@109 b@@64))))
 :qid |unknown.0:0|
 :skolemid |894|
 :pattern ( (|_module.List#Equal| a@@109 b@@64))
)))
(assert (= (type |#_module.Nat.Z|) DatatypeTypeType))
(assert (= (DatatypeCtorId |#_module.Nat.Z|) |##_module.Nat.Z|))
(assert (forall ((d@@18 T@U) ) (!  (=> (= (type d@@18) DatatypeTypeType) (and (=> (_module.Nat.Z_q d@@18) (= (DatatypeCtorId d@@18) |##_module.Nat.Z|)) (=> (= (DatatypeCtorId d@@18) |##_module.Nat.Z|) (_module.Nat.Z_q d@@18))))
 :qid |unknown.0:0|
 :skolemid |895|
 :pattern ( (_module.Nat.Z_q d@@18))
)))
(assert (forall ((d@@19 T@U) ) (!  (=> (and (= (type d@@19) DatatypeTypeType) (_module.Nat.Z_q d@@19)) (= d@@19 |#_module.Nat.Z|))
 :qid |unknown.0:0|
 :skolemid |896|
 :pattern ( (_module.Nat.Z_q d@@19))
)))
(assert (= (type Tclass._module.Nat) TyType))
(assert (= (Tag Tclass._module.Nat) Tagclass._module.Nat))
(assert (forall ((bx@@68 T@U) ) (!  (=> (and (= (type bx@@68) BoxType) ($IsBox bx@@68 Tclass._module.Nat)) (and (= ($Box ($Unbox DatatypeTypeType bx@@68)) bx@@68) ($Is ($Unbox DatatypeTypeType bx@@68) Tclass._module.Nat)))
 :qid |unknown.0:0|
 :skolemid |897|
 :pattern ( ($IsBox bx@@68 Tclass._module.Nat))
)))
(assert ($Is |#_module.Nat.Z| Tclass._module.Nat))
(assert (forall (($h@@23 T@U) ) (!  (=> (and (= (type $h@@23) (MapType0Type refType MapType1Type)) ($IsGoodHeap $h@@23)) ($IsAlloc |#_module.Nat.Z| Tclass._module.Nat $h@@23))
 :qid |DafnyPre.515:12|
 :skolemid |898|
 :pattern ( ($IsAlloc |#_module.Nat.Z| Tclass._module.Nat $h@@23))
)))
(assert (= |#_module.Nat.Z| (Lit |#_module.Nat.Z|)))
(assert (forall ((arg0@@196 T@U) ) (! (= (type (|#_module.Nat.S| arg0@@196)) DatatypeTypeType)
 :qid |funType:#_module.Nat.S|
 :pattern ( (|#_module.Nat.S| arg0@@196))
)))
(assert (forall ((|a#33#0#0| T@U) ) (!  (=> (= (type |a#33#0#0|) DatatypeTypeType) (= (DatatypeCtorId (|#_module.Nat.S| |a#33#0#0|)) |##_module.Nat.S|))
 :qid |SMNADTLi.5:22|
 :skolemid |899|
 :pattern ( (|#_module.Nat.S| |a#33#0#0|))
)))
(assert (forall ((d@@20 T@U) ) (!  (=> (= (type d@@20) DatatypeTypeType) (and (=> (_module.Nat.S_q d@@20) (= (DatatypeCtorId d@@20) |##_module.Nat.S|)) (=> (= (DatatypeCtorId d@@20) |##_module.Nat.S|) (_module.Nat.S_q d@@20))))
 :qid |unknown.0:0|
 :skolemid |900|
 :pattern ( (_module.Nat.S_q d@@20))
)))
(assert (forall ((d@@21 T@U) ) (!  (=> (and (= (type d@@21) DatatypeTypeType) (_module.Nat.S_q d@@21)) (exists ((|a#34#0#0| T@U) ) (!  (and (= (type |a#34#0#0|) DatatypeTypeType) (= d@@21 (|#_module.Nat.S| |a#34#0#0|)))
 :qid |SMNADTLi.5:22|
 :skolemid |901|
 :no-pattern (type |a#34#0#0|)
 :no-pattern (U_2_int |a#34#0#0|)
 :no-pattern (U_2_bool |a#34#0#0|)
)))
 :qid |unknown.0:0|
 :skolemid |902|
 :pattern ( (_module.Nat.S_q d@@21))
)))
(assert (forall ((|a#35#0#0| T@U) ) (!  (=> (= (type |a#35#0#0|) DatatypeTypeType) (and (=> ($Is (|#_module.Nat.S| |a#35#0#0|) Tclass._module.Nat) ($Is |a#35#0#0| Tclass._module.Nat)) (=> ($Is |a#35#0#0| Tclass._module.Nat) ($Is (|#_module.Nat.S| |a#35#0#0|) Tclass._module.Nat))))
 :qid |SMNADTLi.5:22|
 :skolemid |903|
 :pattern ( ($Is (|#_module.Nat.S| |a#35#0#0|) Tclass._module.Nat))
)))
(assert (forall ((|a#36#0#0| T@U) ($h@@24 T@U) ) (!  (=> (and (and (= (type |a#36#0#0|) DatatypeTypeType) (= (type $h@@24) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@24)) (and (=> ($IsAlloc (|#_module.Nat.S| |a#36#0#0|) Tclass._module.Nat $h@@24) ($IsAlloc |a#36#0#0| Tclass._module.Nat $h@@24)) (=> ($IsAlloc |a#36#0#0| Tclass._module.Nat $h@@24) ($IsAlloc (|#_module.Nat.S| |a#36#0#0|) Tclass._module.Nat $h@@24))))
 :qid |SMNADTLi.5:22|
 :skolemid |904|
 :pattern ( ($IsAlloc (|#_module.Nat.S| |a#36#0#0|) Tclass._module.Nat $h@@24))
)))
(assert (forall ((arg0@@197 T@U) ) (! (= (type (_module.Nat._h0 arg0@@197)) DatatypeTypeType)
 :qid |funType:_module.Nat._h0|
 :pattern ( (_module.Nat._h0 arg0@@197))
)))
(assert (forall ((d@@22 T@U) ($h@@25 T@U) ) (!  (=> (and (and (= (type d@@22) DatatypeTypeType) (= (type $h@@25) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@25) (and (_module.Nat.S_q d@@22) ($IsAlloc d@@22 Tclass._module.Nat $h@@25)))) ($IsAlloc (_module.Nat._h0 d@@22) Tclass._module.Nat $h@@25))
 :qid |unknown.0:0|
 :skolemid |905|
 :pattern ( ($IsAlloc (_module.Nat._h0 d@@22) Tclass._module.Nat $h@@25))
)))
(assert (forall ((|a#37#0#0| T@U) ) (!  (=> (= (type |a#37#0#0|) DatatypeTypeType) (= (|#_module.Nat.S| (Lit |a#37#0#0|)) (Lit (|#_module.Nat.S| |a#37#0#0|))))
 :qid |SMNADTLi.5:22|
 :skolemid |906|
 :pattern ( (|#_module.Nat.S| (Lit |a#37#0#0|)))
)))
(assert (forall ((|a#38#0#0| T@U) ) (!  (=> (= (type |a#38#0#0|) DatatypeTypeType) (= (_module.Nat._h0 (|#_module.Nat.S| |a#38#0#0|)) |a#38#0#0|))
 :qid |SMNADTLi.5:22|
 :skolemid |907|
 :pattern ( (|#_module.Nat.S| |a#38#0#0|))
)))
(assert (forall ((|a#39#0#0| T@U) ) (!  (=> (= (type |a#39#0#0|) DatatypeTypeType) (< (DtRank |a#39#0#0|) (DtRank (|#_module.Nat.S| |a#39#0#0|))))
 :qid |SMNADTLi.5:22|
 :skolemid |908|
 :pattern ( (|#_module.Nat.S| |a#39#0#0|))
)))
(assert (forall ((d@@23 T@U) ) (!  (=> (and (= (type d@@23) DatatypeTypeType) (|$IsA#_module.Nat| d@@23)) (or (_module.Nat.Z_q d@@23) (_module.Nat.S_q d@@23)))
 :qid |unknown.0:0|
 :skolemid |909|
 :pattern ( (|$IsA#_module.Nat| d@@23))
)))
(assert (forall ((d@@24 T@U) ) (!  (=> (and (= (type d@@24) DatatypeTypeType) ($Is d@@24 Tclass._module.Nat)) (or (_module.Nat.Z_q d@@24) (_module.Nat.S_q d@@24)))
 :qid |unknown.0:0|
 :skolemid |910|
 :pattern ( (_module.Nat.S_q d@@24) ($Is d@@24 Tclass._module.Nat))
 :pattern ( (_module.Nat.Z_q d@@24) ($Is d@@24 Tclass._module.Nat))
)))
(assert (forall ((a@@110 T@U) (b@@65 T@U) ) (!  (=> (and (and (= (type a@@110) DatatypeTypeType) (= (type b@@65) DatatypeTypeType)) (and (_module.Nat.Z_q a@@110) (_module.Nat.Z_q b@@65))) (and (=> (|_module.Nat#Equal| a@@110 b@@65) true) (=> true (|_module.Nat#Equal| a@@110 b@@65))))
 :qid |unknown.0:0|
 :skolemid |911|
 :pattern ( (|_module.Nat#Equal| a@@110 b@@65) (_module.Nat.Z_q a@@110))
 :pattern ( (|_module.Nat#Equal| a@@110 b@@65) (_module.Nat.Z_q b@@65))
)))
(assert (forall ((a@@111 T@U) (b@@66 T@U) ) (!  (=> (and (and (= (type a@@111) DatatypeTypeType) (= (type b@@66) DatatypeTypeType)) (and (_module.Nat.S_q a@@111) (_module.Nat.S_q b@@66))) (and (=> (|_module.Nat#Equal| a@@111 b@@66) (|_module.Nat#Equal| (_module.Nat._h0 a@@111) (_module.Nat._h0 b@@66))) (=> (|_module.Nat#Equal| (_module.Nat._h0 a@@111) (_module.Nat._h0 b@@66)) (|_module.Nat#Equal| a@@111 b@@66))))
 :qid |unknown.0:0|
 :skolemid |912|
 :pattern ( (|_module.Nat#Equal| a@@111 b@@66) (_module.Nat.S_q a@@111))
 :pattern ( (|_module.Nat#Equal| a@@111 b@@66) (_module.Nat.S_q b@@66))
)))
(assert (forall ((a@@112 T@U) (b@@67 T@U) ) (!  (=> (and (= (type a@@112) DatatypeTypeType) (= (type b@@67) DatatypeTypeType)) (and (=> (|_module.Nat#Equal| a@@112 b@@67) (= a@@112 b@@67)) (=> (= a@@112 b@@67) (|_module.Nat#Equal| a@@112 b@@67))))
 :qid |unknown.0:0|
 :skolemid |913|
 :pattern ( (|_module.Nat#Equal| a@@112 b@@67))
)))
(assert (= (type Tclass._module.__default) TyType))
(assert (= (Tag Tclass._module.__default) Tagclass._module.__default))
(assert (forall ((bx@@69 T@U) ) (!  (=> (and (= (type bx@@69) BoxType) ($IsBox bx@@69 Tclass._module.__default)) (and (= ($Box ($Unbox refType bx@@69)) bx@@69) ($Is ($Unbox refType bx@@69) Tclass._module.__default)))
 :qid |unknown.0:0|
 :skolemid |914|
 :pattern ( ($IsBox bx@@69 Tclass._module.__default))
)))
(assert (forall (($o@@7 T@U) ) (!  (=> (= (type $o@@7) refType) (and (=> ($Is $o@@7 Tclass._module.__default) (or (= $o@@7 null) (= (dtype $o@@7) Tclass._module.__default))) (=> (or (= $o@@7 null) (= (dtype $o@@7) Tclass._module.__default)) ($Is $o@@7 Tclass._module.__default))))
 :qid |unknown.0:0|
 :skolemid |915|
 :pattern ( ($Is $o@@7 Tclass._module.__default))
)))
(assert (forall (($o@@8 T@U) ($h@@26 T@U) ) (!  (=> (and (= (type $o@@8) refType) (= (type $h@@26) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc $o@@8 Tclass._module.__default $h@@26) (or (= $o@@8 null) (U_2_bool (MapType1Select (MapType0Select $h@@26 $o@@8) alloc)))) (=> (or (= $o@@8 null) (U_2_bool (MapType1Select (MapType0Select $h@@26 $o@@8) alloc))) ($IsAlloc $o@@8 Tclass._module.__default $h@@26))))
 :qid |unknown.0:0|
 :skolemid |916|
 :pattern ( ($IsAlloc $o@@8 Tclass._module.__default $h@@26))
)))
(assert  (and (forall ((arg0@@198 Int) ) (! (= (type (_module.__default.int2adt arg0@@198)) BoxType)
 :qid |funType:_module.__default.int2adt|
 :pattern ( (_module.__default.int2adt arg0@@198))
)) (= (type |#$AbInt|) TyType)))
(assert  (=> (<= 3 $FunctionContextHeight) (forall ((|n#0| Int) ) (!  (=> (or (|_module.__default.int2adt#canCall| |n#0|) (not (= 3 $FunctionContextHeight))) ($IsBox (_module.__default.int2adt |n#0|) |#$AbInt|))
 :qid |SMNADTLi.8:26|
 :skolemid |917|
 :pattern ( (_module.__default.int2adt |n#0|))
))))
(assert (forall ((|n#0@@0| Int) ) (!  (and (=> (|_module.__default.int2adt#requires| |n#0@@0|) true) (=> true (|_module.__default.int2adt#requires| |n#0@@0|)))
 :qid |SMNADTLi.8:26|
 :skolemid |918|
 :pattern ( (|_module.__default.int2adt#requires| |n#0@@0|))
)))
(assert (forall ((arg0@@199 T@U) ) (! (= (type (_module.__default.adt2dt arg0@@199)) DatatypeTypeType)
 :qid |funType:_module.__default.adt2dt|
 :pattern ( (_module.__default.adt2dt arg0@@199))
)))
(assert  (=> (<= 2 $FunctionContextHeight) (forall ((|a#0| T@U) ) (!  (=> (and (= (type |a#0|) BoxType) (or (|_module.__default.adt2dt#canCall| |a#0|) (and (not (= 2 $FunctionContextHeight)) ($IsBox |a#0| |#$AbInt|)))) ($Is (_module.__default.adt2dt |a#0|) Tclass._module.Nat))
 :qid |SMNADTLi.9:25|
 :skolemid |919|
 :pattern ( (_module.__default.adt2dt |a#0|))
))))
(assert (forall ((|a#0@@0| T@U) ) (!  (=> (and (= (type |a#0@@0|) BoxType) ($IsBox |a#0@@0| |#$AbInt|)) (and (=> (|_module.__default.adt2dt#requires| |a#0@@0|) true) (=> true (|_module.__default.adt2dt#requires| |a#0@@0|))))
 :qid |SMNADTLi.9:25|
 :skolemid |920|
 :pattern ( (|_module.__default.adt2dt#requires| |a#0@@0|))
)))
(assert  (=> (<= 22 $FunctionContextHeight) (forall ((|n#0@@1| T@U) ) (!  (=> (and (= (type |n#0@@1|) BoxType) (or (|_module.__default.AbIsZero#canCall| |n#0@@1|) (and (not (= 22 $FunctionContextHeight)) ($IsBox |n#0@@1| |#$AbInt|)))) true)
 :qid |SMNADTLi.14:21|
 :skolemid |921|
 :pattern ( (_module.__default.AbIsZero |n#0@@1|))
))))
(assert (forall ((|n#0@@2| T@U) ) (!  (=> (and (= (type |n#0@@2|) BoxType) ($IsBox |n#0@@2| |#$AbInt|)) (and (=> (|_module.__default.AbIsZero#requires| |n#0@@2|) true) (=> true (|_module.__default.AbIsZero#requires| |n#0@@2|))))
 :qid |SMNADTLi.14:21|
 :skolemid |922|
 :pattern ( (|_module.__default.AbIsZero#requires| |n#0@@2|))
)))
(assert  (=> (<= 22 $FunctionContextHeight) (forall ((|n#0@@3| T@U) ) (!  (=> (and (= (type |n#0@@3|) BoxType) (or (|_module.__default.AbIsZero#canCall| |n#0@@3|) (and (not (= 22 $FunctionContextHeight)) ($IsBox |n#0@@3| |#$AbInt|)))) (and (|_module.__default.int2adt#canCall| (LitInt 0)) (and (=> (_module.__default.AbIsZero |n#0@@3|) (= |n#0@@3| (_module.__default.int2adt (LitInt 0)))) (=> (= |n#0@@3| (_module.__default.int2adt (LitInt 0))) (_module.__default.AbIsZero |n#0@@3|)))))
 :qid |SMNADTLi.14:21|
 :skolemid |923|
 :pattern ( (_module.__default.AbIsZero |n#0@@3|))
))))
(assert  (=> (<= 22 $FunctionContextHeight) (forall ((|n#0@@4| T@U) ) (!  (=> (and (= (type |n#0@@4|) BoxType) (or (|_module.__default.AbIsZero#canCall| (Lit |n#0@@4|)) (and (not (= 22 $FunctionContextHeight)) ($IsBox |n#0@@4| |#$AbInt|)))) (and (|_module.__default.int2adt#canCall| (LitInt 0)) (and (=> (_module.__default.AbIsZero (Lit |n#0@@4|)) (= (Lit |n#0@@4|) (_module.__default.int2adt (LitInt 0)))) (=> (= (Lit |n#0@@4|) (_module.__default.int2adt (LitInt 0))) (_module.__default.AbIsZero (Lit |n#0@@4|))))))
 :qid |SMNADTLi.14:21|
 :weight 3
 :skolemid |924|
 :pattern ( (_module.__default.AbIsZero (Lit |n#0@@4|)))
))))
(assert  (=> (<= 23 $FunctionContextHeight) (forall ((|n#0@@5| T@U) ) (!  (=> (and (= (type |n#0@@5|) BoxType) (or (|_module.__default.AbPos#canCall| |n#0@@5|) (and (not (= 23 $FunctionContextHeight)) ($IsBox |n#0@@5| |#$AbInt|)))) true)
 :qid |SMNADTLi.15:18|
 :skolemid |926|
 :pattern ( (_module.__default.AbPos |n#0@@5|))
))))
(assert (forall ((|n#0@@6| T@U) ) (!  (=> (and (= (type |n#0@@6|) BoxType) ($IsBox |n#0@@6| |#$AbInt|)) (and (=> (|_module.__default.AbPos#requires| |n#0@@6|) true) (=> true (|_module.__default.AbPos#requires| |n#0@@6|))))
 :qid |SMNADTLi.15:18|
 :skolemid |927|
 :pattern ( (|_module.__default.AbPos#requires| |n#0@@6|))
)))
(assert  (=> (<= 23 $FunctionContextHeight) (forall ((|n#0@@7| T@U) ) (!  (=> (and (= (type |n#0@@7|) BoxType) (or (|_module.__default.AbPos#canCall| |n#0@@7|) (and (not (= 23 $FunctionContextHeight)) ($IsBox |n#0@@7| |#$AbInt|)))) (and (|_module.__default.AbIsZero#canCall| |n#0@@7|) (and (=> (_module.__default.AbPos |n#0@@7|) (not (_module.__default.AbIsZero |n#0@@7|))) (=> (not (_module.__default.AbIsZero |n#0@@7|)) (_module.__default.AbPos |n#0@@7|)))))
 :qid |SMNADTLi.15:18|
 :skolemid |928|
 :pattern ( (_module.__default.AbPos |n#0@@7|))
))))
(assert  (=> (<= 23 $FunctionContextHeight) (forall ((|n#0@@8| T@U) ) (!  (=> (and (= (type |n#0@@8|) BoxType) (or (|_module.__default.AbPos#canCall| (Lit |n#0@@8|)) (and (not (= 23 $FunctionContextHeight)) ($IsBox |n#0@@8| |#$AbInt|)))) (and (|_module.__default.AbIsZero#canCall| (Lit |n#0@@8|)) (and (=> (_module.__default.AbPos (Lit |n#0@@8|)) (not (U_2_bool (Lit (bool_2_U (_module.__default.AbIsZero (Lit |n#0@@8|))))))) (=> (not (U_2_bool (Lit (bool_2_U (_module.__default.AbIsZero (Lit |n#0@@8|)))))) (_module.__default.AbPos (Lit |n#0@@8|))))))
 :qid |SMNADTLi.15:18|
 :weight 3
 :skolemid |929|
 :pattern ( (_module.__default.AbPos (Lit |n#0@@8|)))
))))
(assert  (=> (<= 11 $FunctionContextHeight) (forall ((|n#0@@9| T@U) (|m#0| T@U) ) (!  (=> (and (and (= (type |n#0@@9|) BoxType) (= (type |m#0|) BoxType)) (or (|_module.__default.AbLt#canCall| |n#0@@9| |m#0|) (and (not (= 11 $FunctionContextHeight)) (and ($IsBox |n#0@@9| |#$AbInt|) ($IsBox |m#0| |#$AbInt|))))) true)
 :qid |SMNADTLi.18:22|
 :skolemid |931|
 :pattern ( (_module.__default.AbLt |n#0@@9| |m#0|))
))))
(assert (forall ((|n#0@@10| T@U) (|m#0@@0| T@U) ) (!  (=> (and (and (= (type |n#0@@10|) BoxType) (= (type |m#0@@0|) BoxType)) (and ($IsBox |n#0@@10| |#$AbInt|) ($IsBox |m#0@@0| |#$AbInt|))) (and (=> (|_module.__default.AbLt#requires| |n#0@@10| |m#0@@0|) true) (=> true (|_module.__default.AbLt#requires| |n#0@@10| |m#0@@0|))))
 :qid |SMNADTLi.18:22|
 :skolemid |932|
 :pattern ( (|_module.__default.AbLt#requires| |n#0@@10| |m#0@@0|))
)))
(assert (forall ((arg0@@200 T@U) ) (! (= (type (_module.__default.AbInc1 arg0@@200)) BoxType)
 :qid |funType:_module.__default.AbInc1|
 :pattern ( (_module.__default.AbInc1 arg0@@200))
)))
(assert  (=> (<= 4 $FunctionContextHeight) (forall ((|n#0@@11| T@U) ) (!  (=> (and (= (type |n#0@@11|) BoxType) (or (|_module.__default.AbInc1#canCall| |n#0@@11|) (and (not (= 4 $FunctionContextHeight)) ($IsBox |n#0@@11| |#$AbInt|)))) ($IsBox (_module.__default.AbInc1 |n#0@@11|) |#$AbInt|))
 :qid |SMNADTLi.19:24|
 :skolemid |933|
 :pattern ( (_module.__default.AbInc1 |n#0@@11|))
))))
(assert (forall ((|n#0@@12| T@U) ) (!  (=> (and (= (type |n#0@@12|) BoxType) ($IsBox |n#0@@12| |#$AbInt|)) (and (=> (|_module.__default.AbInc1#requires| |n#0@@12|) true) (=> true (|_module.__default.AbInc1#requires| |n#0@@12|))))
 :qid |SMNADTLi.19:24|
 :skolemid |934|
 :pattern ( (|_module.__default.AbInc1#requires| |n#0@@12|))
)))
(assert (forall ((arg0@@201 T@U) (arg1@@91 T@U) ) (! (= (type (_module.__default.AbInc arg0@@201 arg1@@91)) BoxType)
 :qid |funType:_module.__default.AbInc|
 :pattern ( (_module.__default.AbInc arg0@@201 arg1@@91))
)))
(assert  (=> (<= 7 $FunctionContextHeight) (forall ((|n#0@@13| T@U) (|m#0@@1| T@U) ) (!  (=> (and (and (= (type |n#0@@13|) BoxType) (= (type |m#0@@1|) BoxType)) (or (|_module.__default.AbInc#canCall| |n#0@@13| |m#0@@1|) (and (not (= 7 $FunctionContextHeight)) (and ($IsBox |n#0@@13| |#$AbInt|) ($IsBox |m#0@@1| |#$AbInt|))))) ($IsBox (_module.__default.AbInc |n#0@@13| |m#0@@1|) |#$AbInt|))
 :qid |SMNADTLi.20:23|
 :skolemid |935|
 :pattern ( (_module.__default.AbInc |n#0@@13| |m#0@@1|))
))))
(assert (forall ((|n#0@@14| T@U) (|m#0@@2| T@U) ) (!  (=> (and (and (= (type |n#0@@14|) BoxType) (= (type |m#0@@2|) BoxType)) (and ($IsBox |n#0@@14| |#$AbInt|) ($IsBox |m#0@@2| |#$AbInt|))) (and (=> (|_module.__default.AbInc#requires| |n#0@@14| |m#0@@2|) true) (=> true (|_module.__default.AbInc#requires| |n#0@@14| |m#0@@2|))))
 :qid |SMNADTLi.20:23|
 :skolemid |936|
 :pattern ( (|_module.__default.AbInc#requires| |n#0@@14| |m#0@@2|))
)))
(assert (forall ((arg0@@202 T@U) (arg1@@92 T@U) ) (! (= (type (_module.__default.AbDec arg0@@202 arg1@@92)) BoxType)
 :qid |funType:_module.__default.AbDec|
 :pattern ( (_module.__default.AbDec arg0@@202 arg1@@92))
)))
(assert  (=> (<= 31 $FunctionContextHeight) (forall ((|n#0@@15| T@U) (|m#0@@3| T@U) ) (!  (=> (and (and (= (type |n#0@@15|) BoxType) (= (type |m#0@@3|) BoxType)) (or (|_module.__default.AbDec#canCall| |n#0@@15| |m#0@@3|) (and (not (= 31 $FunctionContextHeight)) (and ($IsBox |n#0@@15| |#$AbInt|) ($IsBox |m#0@@3| |#$AbInt|))))) ($IsBox (_module.__default.AbDec |n#0@@15| |m#0@@3|) |#$AbInt|))
 :qid |SMNADTLi.21:23|
 :skolemid |937|
 :pattern ( (_module.__default.AbDec |n#0@@15| |m#0@@3|))
))))
(assert (forall ((|n#0@@16| T@U) (|m#0@@4| T@U) ) (!  (=> (and (and (= (type |n#0@@16|) BoxType) (= (type |m#0@@4|) BoxType)) (and ($IsBox |n#0@@16| |#$AbInt|) ($IsBox |m#0@@4| |#$AbInt|))) (and (=> (|_module.__default.AbDec#requires| |n#0@@16| |m#0@@4|) true) (=> true (|_module.__default.AbDec#requires| |n#0@@16| |m#0@@4|))))
 :qid |SMNADTLi.21:23|
 :skolemid |938|
 :pattern ( (|_module.__default.AbDec#requires| |n#0@@16| |m#0@@4|))
)))
(assert (forall ((arg0@@203 T@U) ) (! (= (type (_module.__default.AbDiv2 arg0@@203)) BoxType)
 :qid |funType:_module.__default.AbDiv2|
 :pattern ( (_module.__default.AbDiv2 arg0@@203))
)))
(assert  (=> (<= 19 $FunctionContextHeight) (forall ((|n#0@@17| T@U) ) (!  (=> (and (= (type |n#0@@17|) BoxType) (or (|_module.__default.AbDiv2#canCall| |n#0@@17|) (and (not (= 19 $FunctionContextHeight)) ($IsBox |n#0@@17| |#$AbInt|)))) (and (or (_module.__default.AbLt (_module.__default.AbInc (_module.__default.AbDiv2 |n#0@@17|) (_module.__default.AbDiv2 |n#0@@17|)) |n#0@@17|) (= (_module.__default.AbInc (_module.__default.AbDiv2 |n#0@@17|) (_module.__default.AbDiv2 |n#0@@17|)) |n#0@@17|)) ($IsBox (_module.__default.AbDiv2 |n#0@@17|) |#$AbInt|)))
 :qid |SMNADTLi.22:24|
 :skolemid |939|
 :pattern ( (_module.__default.AbDiv2 |n#0@@17|))
))))
(assert (forall ((|n#0@@18| T@U) ) (!  (=> (and (= (type |n#0@@18|) BoxType) ($IsBox |n#0@@18| |#$AbInt|)) (and (=> (|_module.__default.AbDiv2#requires| |n#0@@18|) true) (=> true (|_module.__default.AbDiv2#requires| |n#0@@18|))))
 :qid |SMNADTLi.22:24|
 :skolemid |940|
 :pattern ( (|_module.__default.AbDiv2#requires| |n#0@@18|))
)))
(assert (forall ((arg0@@204 T@U) ) (! (= (type (_module.__default.AbSetLen arg0@@204)) BoxType)
 :qid |funType:_module.__default.AbSetLen|
 :pattern ( (_module.__default.AbSetLen arg0@@204))
)))
(assert  (=> (<= 16 $FunctionContextHeight) (forall ((|s#0| T@U) ) (!  (=> (and (= (type |s#0|) (MapType0Type BoxType boolType)) (or (|_module.__default.AbSetLen#canCall| |s#0|) (and (not (= 16 $FunctionContextHeight)) ($Is |s#0| (TSet |#$AbInt|))))) ($IsBox (_module.__default.AbSetLen |s#0|) |#$AbInt|))
 :qid |SMNADTLi.24:26|
 :skolemid |941|
 :pattern ( (_module.__default.AbSetLen |s#0|))
))))
(assert (forall ((|s#0@@0| T@U) ) (!  (=> (and (= (type |s#0@@0|) (MapType0Type BoxType boolType)) ($Is |s#0@@0| (TSet |#$AbInt|))) (and (=> (|_module.__default.AbSetLen#requires| |s#0@@0|) true) (=> true (|_module.__default.AbSetLen#requires| |s#0@@0|))))
 :qid |SMNADTLi.24:26|
 :skolemid |942|
 :pattern ( (|_module.__default.AbSetLen#requires| |s#0@@0|))
)))
(assert (forall ((arg0@@205 T@U) (arg1@@93 T@U) ) (! (= (type (_module.__default.AbBoundSet arg0@@205 arg1@@93)) (MapType0Type BoxType boolType))
 :qid |funType:_module.__default.AbBoundSet|
 :pattern ( (_module.__default.AbBoundSet arg0@@205 arg1@@93))
)))
(assert  (=> (<= 35 $FunctionContextHeight) (forall ((|lo#0| T@U) (|len#0| T@U) ) (!  (=> (and (and (= (type |lo#0|) BoxType) (= (type |len#0|) BoxType)) (or (|_module.__default.AbBoundSet#canCall| |lo#0| |len#0|) (and (not (= 35 $FunctionContextHeight)) (and ($IsBox |lo#0| |#$AbInt|) ($IsBox |len#0| |#$AbInt|))))) (and (and (= (_module.__default.AbSetLen (_module.__default.AbBoundSet |lo#0| |len#0|)) |len#0|) (forall ((|x#0@@1| T@U) ) (!  (=> (and (= (type |x#0@@1|) BoxType) ($IsBox |x#0@@1| |#$AbInt|)) (and (=> (and (or (_module.__default.AbLt |lo#0| |x#0@@1|) (= |lo#0| |x#0@@1|)) (_module.__default.AbLt |x#0@@1| (_module.__default.AbInc |lo#0| |len#0|))) (U_2_bool (MapType0Select (_module.__default.AbBoundSet |lo#0| |len#0|) |x#0@@1|))) (=> (U_2_bool (MapType0Select (_module.__default.AbBoundSet |lo#0| |len#0|) |x#0@@1|)) (and (or (_module.__default.AbLt |lo#0| |x#0@@1|) (= |lo#0| |x#0@@1|)) (_module.__default.AbLt |x#0@@1| (_module.__default.AbInc |lo#0| |len#0|))))))
 :qid |SMNADTLi.34:18|
 :skolemid |952|
 :pattern ( (MapType0Select (_module.__default.AbBoundSet |lo#0| |len#0|) |x#0@@1|))
 :pattern ( (_module.__default.AbLt |x#0@@1| (_module.__default.AbInc |lo#0| |len#0|)))
 :pattern ( (_module.__default.AbLt |lo#0| |x#0@@1|))
))) ($Is (_module.__default.AbBoundSet |lo#0| |len#0|) (TSet |#$AbInt|))))
 :qid |SMNADTLi.32:28|
 :skolemid |953|
 :pattern ( (_module.__default.AbBoundSet |lo#0| |len#0|))
))))
(assert (forall ((|lo#0@@0| T@U) (|len#0@@0| T@U) ) (!  (=> (and (and (= (type |lo#0@@0|) BoxType) (= (type |len#0@@0|) BoxType)) (and ($IsBox |lo#0@@0| |#$AbInt|) ($IsBox |len#0@@0| |#$AbInt|))) (and (=> (|_module.__default.AbBoundSet#requires| |lo#0@@0| |len#0@@0|) true) (=> true (|_module.__default.AbBoundSet#requires| |lo#0@@0| |len#0@@0|))))
 :qid |SMNADTLi.32:28|
 :skolemid |954|
 :pattern ( (|_module.__default.AbBoundSet#requires| |lo#0@@0| |len#0@@0|))
)))
(assert (forall ((arg0@@206 T@U) (arg1@@94 T@U) ) (! (= (type (_module.__default.Length arg0@@206 arg1@@94)) BoxType)
 :qid |funType:_module.__default.Length|
 :pattern ( (_module.__default.Length arg0@@206 arg1@@94))
)))
(assert (forall (($ly T@U) (|xs#0| T@U) ) (!  (=> (and (= (type $ly) LayerTypeType) (= (type |xs#0|) DatatypeTypeType)) (= (_module.__default.Length ($LS $ly) |xs#0|) (_module.__default.Length $ly |xs#0|)))
 :qid |SMNADTLi.102:17|
 :skolemid |1020|
 :pattern ( (_module.__default.Length ($LS $ly) |xs#0|))
)))
(assert  (and (forall ((arg0@@207 T@U) ) (! (= (type (AsFuelBottom arg0@@207)) LayerTypeType)
 :qid |funType:AsFuelBottom|
 :pattern ( (AsFuelBottom arg0@@207))
)) (= (type $LZ) LayerTypeType)))
(assert (forall (($ly@@0 T@U) (|xs#0@@0| T@U) ) (!  (=> (and (= (type $ly@@0) LayerTypeType) (= (type |xs#0@@0|) DatatypeTypeType)) (= (_module.__default.Length $ly@@0 |xs#0@@0|) (_module.__default.Length $LZ |xs#0@@0|)))
 :qid |SMNADTLi.102:17|
 :skolemid |1021|
 :pattern ( (_module.__default.Length (AsFuelBottom $ly@@0) |xs#0@@0|))
)))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@1 T@U) (|xs#0@@1| T@U) ) (!  (=> (and (and (= (type $ly@@1) LayerTypeType) (= (type |xs#0@@1|) DatatypeTypeType)) (or (|_module.__default.Length#canCall| |xs#0@@1|) (and (not (= 5 $FunctionContextHeight)) ($Is |xs#0@@1| (Tclass._module.List |#$AbInt|))))) ($IsBox (_module.__default.Length $ly@@1 |xs#0@@1|) |#$AbInt|))
 :qid |SMNADTLi.102:17|
 :skolemid |1022|
 :pattern ( (_module.__default.Length $ly@@1 |xs#0@@1|))
))))
(assert (forall (($ly@@2 T@U) (|xs#0@@2| T@U) ) (!  (=> (and (and (= (type $ly@@2) LayerTypeType) (= (type |xs#0@@2|) DatatypeTypeType)) ($Is |xs#0@@2| (Tclass._module.List |#$AbInt|))) (and (=> (|_module.__default.Length#requires| $ly@@2 |xs#0@@2|) true) (=> true (|_module.__default.Length#requires| $ly@@2 |xs#0@@2|))))
 :qid |SMNADTLi.102:17|
 :skolemid |1023|
 :pattern ( (|_module.__default.Length#requires| $ly@@2 |xs#0@@2|))
)))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@3 T@U) (|xs#0@@3| T@U) ) (!  (=> (and (and (= (type $ly@@3) LayerTypeType) (= (type |xs#0@@3|) DatatypeTypeType)) (or (|_module.__default.Length#canCall| |xs#0@@3|) (and (not (= 5 $FunctionContextHeight)) ($Is |xs#0@@3| (Tclass._module.List |#$AbInt|))))) (and (and (=> (_module.List.Nil_q |xs#0@@3|) (|_module.__default.int2adt#canCall| (LitInt 0))) (=> (not (_module.List.Nil_q |xs#0@@3|)) (let ((|tail#1| (_module.List.tail |xs#0@@3|)))
 (and (|_module.__default.Length#canCall| |tail#1|) (|_module.__default.AbInc1#canCall| (_module.__default.Length $ly@@3 |tail#1|)))))) (= (_module.__default.Length ($LS $ly@@3) |xs#0@@3|) (ite (_module.List.Nil_q |xs#0@@3|) (_module.__default.int2adt (LitInt 0)) (let ((|tail#0| (_module.List.tail |xs#0@@3|)))
(_module.__default.AbInc1 (_module.__default.Length $ly@@3 |tail#0|)))))))
 :qid |SMNADTLi.102:17|
 :skolemid |1024|
 :pattern ( (_module.__default.Length ($LS $ly@@3) |xs#0@@3|))
))))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@4 T@U) (|xs#0@@4| T@U) ) (!  (=> (and (and (= (type $ly@@4) LayerTypeType) (= (type |xs#0@@4|) DatatypeTypeType)) (or (|_module.__default.Length#canCall| (Lit |xs#0@@4|)) (and (not (= 5 $FunctionContextHeight)) ($Is |xs#0@@4| (Tclass._module.List |#$AbInt|))))) (and (and (=> (U_2_bool (Lit (bool_2_U (_module.List.Nil_q (Lit |xs#0@@4|))))) (|_module.__default.int2adt#canCall| (LitInt 0))) (=> (not (U_2_bool (Lit (bool_2_U (_module.List.Nil_q (Lit |xs#0@@4|)))))) (let ((|tail#3| (Lit (_module.List.tail (Lit |xs#0@@4|)))))
 (and (|_module.__default.Length#canCall| |tail#3|) (|_module.__default.AbInc1#canCall| (_module.__default.Length ($LS $ly@@4) |tail#3|)))))) (= (_module.__default.Length ($LS $ly@@4) (Lit |xs#0@@4|)) (ite (_module.List.Nil_q (Lit |xs#0@@4|)) (_module.__default.int2adt (LitInt 0)) (let ((|tail#2| (Lit (_module.List.tail (Lit |xs#0@@4|)))))
(_module.__default.AbInc1 (Lit (_module.__default.Length ($LS $ly@@4) |tail#2|))))))))
 :qid |SMNADTLi.102:17|
 :weight 3
 :skolemid |1025|
 :pattern ( (_module.__default.Length ($LS $ly@@4) (Lit |xs#0@@4|)))
))))
(assert (forall ((arg0@@208 T@U) (arg1@@95 T@U) (arg2@@46 T@U) ) (! (= (type (_module.__default.Split arg0@@208 arg1@@95 arg2@@46)) DatatypeTypeType)
 :qid |funType:_module.__default.Split|
 :pattern ( (_module.__default.Split arg0@@208 arg1@@95 arg2@@46))
)))
(assert (forall (($ly@@5 T@U) (|xs#0@@5| T@U) (|b#0| T@U) ) (!  (=> (and (and (= (type $ly@@5) LayerTypeType) (= (type |xs#0@@5|) DatatypeTypeType)) (= (type |b#0|) BoxType)) (= (_module.__default.Split ($LS $ly@@5) |xs#0@@5| |b#0|) (_module.__default.Split $ly@@5 |xs#0@@5| |b#0|)))
 :qid |SMNADTLi.109:17|
 :skolemid |1029|
 :pattern ( (_module.__default.Split ($LS $ly@@5) |xs#0@@5| |b#0|))
)))
(assert (forall (($ly@@6 T@U) (|xs#0@@6| T@U) (|b#0@@0| T@U) ) (!  (=> (and (and (= (type $ly@@6) LayerTypeType) (= (type |xs#0@@6|) DatatypeTypeType)) (= (type |b#0@@0|) BoxType)) (= (_module.__default.Split $ly@@6 |xs#0@@6| |b#0@@0|) (_module.__default.Split $LZ |xs#0@@6| |b#0@@0|)))
 :qid |SMNADTLi.109:17|
 :skolemid |1030|
 :pattern ( (_module.__default.Split (AsFuelBottom $ly@@6) |xs#0@@6| |b#0@@0|))
)))
(assert  (=> (<= 12 $FunctionContextHeight) (forall (($ly@@7 T@U) (|xs#0@@7| T@U) (|b#0@@1| T@U) ) (!  (=> (and (and (and (= (type $ly@@7) LayerTypeType) (= (type |xs#0@@7|) DatatypeTypeType)) (= (type |b#0@@1|) BoxType)) (or (|_module.__default.Split#canCall| |xs#0@@7| |b#0@@1|) (and (not (= 12 $FunctionContextHeight)) (and ($Is |xs#0@@7| (Tclass._module.List |#$AbInt|)) ($IsBox |b#0@@1| |#$AbInt|))))) (and (let ((|r#0| (_module.__default.Split $ly@@7 |xs#0@@7| |b#0@@1|)))
(= (_module.__default.Length ($LS $LZ) |xs#0@@7|) (_module.__default.AbInc (_module.__default.Length ($LS $LZ) ($Unbox DatatypeTypeType (_System.Tuple2._0 |r#0|))) (_module.__default.Length ($LS $LZ) ($Unbox DatatypeTypeType (_System.Tuple2._1 |r#0|)))))) ($Is (_module.__default.Split $ly@@7 |xs#0@@7| |b#0@@1|) (Tclass._System.Tuple2 (Tclass._module.List |#$AbInt|) (Tclass._module.List |#$AbInt|)))))
 :qid |SMNADTLi.109:17|
 :skolemid |1031|
 :pattern ( (_module.__default.Split $ly@@7 |xs#0@@7| |b#0@@1|))
))))
(assert (forall (($ly@@8 T@U) (|xs#0@@8| T@U) (|b#0@@2| T@U) ) (!  (=> (and (and (and (= (type $ly@@8) LayerTypeType) (= (type |xs#0@@8|) DatatypeTypeType)) (= (type |b#0@@2|) BoxType)) (and ($Is |xs#0@@8| (Tclass._module.List |#$AbInt|)) ($IsBox |b#0@@2| |#$AbInt|))) (and (=> (|_module.__default.Split#requires| $ly@@8 |xs#0@@8| |b#0@@2|) true) (=> true (|_module.__default.Split#requires| $ly@@8 |xs#0@@8| |b#0@@2|))))
 :qid |SMNADTLi.109:17|
 :skolemid |1032|
 :pattern ( (|_module.__default.Split#requires| $ly@@8 |xs#0@@8| |b#0@@2|))
)))
(assert  (=> (<= 12 $FunctionContextHeight) (forall (($ly@@9 T@U) (|xs#0@@9| T@U) (|b#0@@3| T@U) ) (!  (=> (and (and (and (= (type $ly@@9) LayerTypeType) (= (type |xs#0@@9|) DatatypeTypeType)) (= (type |b#0@@3|) BoxType)) (or (|_module.__default.Split#canCall| |xs#0@@9| |b#0@@3|) (and (not (= 12 $FunctionContextHeight)) (and ($Is |xs#0@@9| (Tclass._module.List |#$AbInt|)) ($IsBox |b#0@@3| |#$AbInt|))))) (and (=> (not (_module.List.Nil_q |xs#0@@9|)) (let ((|tail#1@@0| (_module.List.tail |xs#0@@9|)))
(let ((|x#1| (_module.List.head |xs#0@@9|)))
 (and (|_module.__default.Split#canCall| |tail#1@@0| |b#0@@3|) (|_module.__default.AbLt#canCall| |x#1| |b#0@@3|))))) (= (_module.__default.Split ($LS $ly@@9) |xs#0@@9| |b#0@@3|) (ite (_module.List.Nil_q |xs#0@@9|) (|#_System._tuple#2._#Make2| ($Box (Lit |#_module.List.Nil|)) ($Box (Lit |#_module.List.Nil|))) (let ((|tail#0@@0| (_module.List.tail |xs#0@@9|)))
(let ((|x#0@@2| (_module.List.head |xs#0@@9|)))
(let ((|R#0| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split $ly@@9 |tail#0@@0| |b#0@@3|)))))
(let ((|L#0| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split $ly@@9 |tail#0@@0| |b#0@@3|)))))
(ite (_module.__default.AbLt |x#0@@2| |b#0@@3|) (|#_System._tuple#2._#Make2| ($Box (|#_module.List.Cons| |x#0@@2| |L#0|)) ($Box |R#0|)) (|#_System._tuple#2._#Make2| ($Box |L#0|) ($Box (|#_module.List.Cons| |x#0@@2| |R#0|))))))))))))
 :qid |SMNADTLi.109:17|
 :skolemid |1033|
 :pattern ( (_module.__default.Split ($LS $ly@@9) |xs#0@@9| |b#0@@3|))
))))
(assert  (=> (<= 12 $FunctionContextHeight) (forall (($ly@@10 T@U) (|xs#0@@10| T@U) (|b#0@@4| T@U) ) (!  (=> (and (and (and (= (type $ly@@10) LayerTypeType) (= (type |xs#0@@10|) DatatypeTypeType)) (= (type |b#0@@4|) BoxType)) (or (|_module.__default.Split#canCall| (Lit |xs#0@@10|) |b#0@@4|) (and (not (= 12 $FunctionContextHeight)) (and ($Is |xs#0@@10| (Tclass._module.List |#$AbInt|)) ($IsBox |b#0@@4| |#$AbInt|))))) (and (=> (not (U_2_bool (Lit (bool_2_U (_module.List.Nil_q (Lit |xs#0@@10|)))))) (let ((|tail#3@@0| (Lit (_module.List.tail (Lit |xs#0@@10|)))))
(let ((|x#3| (Lit (_module.List.head (Lit |xs#0@@10|)))))
 (and (|_module.__default.Split#canCall| |tail#3@@0| |b#0@@4|) (|_module.__default.AbLt#canCall| |x#3| |b#0@@4|))))) (= (_module.__default.Split ($LS $ly@@10) (Lit |xs#0@@10|) |b#0@@4|) (ite (_module.List.Nil_q (Lit |xs#0@@10|)) (|#_System._tuple#2._#Make2| ($Box (Lit |#_module.List.Nil|)) ($Box (Lit |#_module.List.Nil|))) (let ((|tail#2@@0| (Lit (_module.List.tail (Lit |xs#0@@10|)))))
(let ((|x#2| (Lit (_module.List.head (Lit |xs#0@@10|)))))
(let ((|R#2| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $ly@@10) |tail#2@@0| |b#0@@4|)))))
(let ((|L#2| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $ly@@10) |tail#2@@0| |b#0@@4|)))))
(ite (_module.__default.AbLt |x#2| |b#0@@4|) (|#_System._tuple#2._#Make2| ($Box (|#_module.List.Cons| |x#2| |L#2|)) ($Box |R#2|)) (|#_System._tuple#2._#Make2| ($Box |L#2|) ($Box (|#_module.List.Cons| |x#2| |R#2|))))))))))))
 :qid |SMNADTLi.109:17|
 :weight 3
 :skolemid |1034|
 :pattern ( (_module.__default.Split ($LS $ly@@10) (Lit |xs#0@@10|) |b#0@@4|))
))))
(assert  (=> (<= 12 $FunctionContextHeight) (forall (($ly@@11 T@U) (|xs#0@@11| T@U) (|b#0@@5| T@U) ) (!  (=> (and (and (and (= (type $ly@@11) LayerTypeType) (= (type |xs#0@@11|) DatatypeTypeType)) (= (type |b#0@@5|) BoxType)) (or (|_module.__default.Split#canCall| (Lit |xs#0@@11|) (Lit |b#0@@5|)) (and (not (= 12 $FunctionContextHeight)) (and ($Is |xs#0@@11| (Tclass._module.List |#$AbInt|)) ($IsBox |b#0@@5| |#$AbInt|))))) (and (=> (not (U_2_bool (Lit (bool_2_U (_module.List.Nil_q (Lit |xs#0@@11|)))))) (let ((|tail#5| (Lit (_module.List.tail (Lit |xs#0@@11|)))))
(let ((|x#5| (Lit (_module.List.head (Lit |xs#0@@11|)))))
 (and (|_module.__default.Split#canCall| |tail#5| (Lit |b#0@@5|)) (|_module.__default.AbLt#canCall| |x#5| (Lit |b#0@@5|)))))) (= (_module.__default.Split ($LS $ly@@11) (Lit |xs#0@@11|) (Lit |b#0@@5|)) (ite (_module.List.Nil_q (Lit |xs#0@@11|)) (|#_System._tuple#2._#Make2| ($Box (Lit |#_module.List.Nil|)) ($Box (Lit |#_module.List.Nil|))) (let ((|tail#4| (Lit (_module.List.tail (Lit |xs#0@@11|)))))
(let ((|x#4| (Lit (_module.List.head (Lit |xs#0@@11|)))))
(let ((|R#4| ($Unbox DatatypeTypeType (_System.Tuple2._1 (Lit (_module.__default.Split ($LS $ly@@11) |tail#4| (Lit |b#0@@5|)))))))
(let ((|L#4| ($Unbox DatatypeTypeType (_System.Tuple2._0 (Lit (_module.__default.Split ($LS $ly@@11) |tail#4| (Lit |b#0@@5|)))))))
(ite (_module.__default.AbLt |x#4| (Lit |b#0@@5|)) (|#_System._tuple#2._#Make2| ($Box (|#_module.List.Cons| |x#4| |L#4|)) ($Box |R#4|)) (|#_System._tuple#2._#Make2| ($Box |L#4|) ($Box (|#_module.List.Cons| |x#4| |R#4|))))))))))))
 :qid |SMNADTLi.109:17|
 :weight 3
 :skolemid |1035|
 :pattern ( (_module.__default.Split ($LS $ly@@11) (Lit |xs#0@@11|) (Lit |b#0@@5|)))
))))
(assert (forall ((arg0@@209 T@U) (arg1@@96 T@U) ) (! (= (type (_module.__default.Elements arg0@@209 arg1@@96)) (MapType0Type BoxType boolType))
 :qid |funType:_module.__default.Elements|
 :pattern ( (_module.__default.Elements arg0@@209 arg1@@96))
)))
(assert (forall (($ly@@12 T@U) (|xs#0@@12| T@U) ) (!  (=> (and (= (type $ly@@12) LayerTypeType) (= (type |xs#0@@12|) DatatypeTypeType)) (= (_module.__default.Elements ($LS $ly@@12) |xs#0@@12|) (_module.__default.Elements $ly@@12 |xs#0@@12|)))
 :qid |SMNADTLi.138:10|
 :skolemid |1044|
 :pattern ( (_module.__default.Elements ($LS $ly@@12) |xs#0@@12|))
)))
(assert (forall (($ly@@13 T@U) (|xs#0@@13| T@U) ) (!  (=> (and (= (type $ly@@13) LayerTypeType) (= (type |xs#0@@13|) DatatypeTypeType)) (= (_module.__default.Elements $ly@@13 |xs#0@@13|) (_module.__default.Elements $LZ |xs#0@@13|)))
 :qid |SMNADTLi.138:10|
 :skolemid |1045|
 :pattern ( (_module.__default.Elements (AsFuelBottom $ly@@13) |xs#0@@13|))
)))
(assert  (=> (<= 13 $FunctionContextHeight) (forall (($ly@@14 T@U) (|xs#0@@14| T@U) ) (!  (=> (and (and (= (type $ly@@14) LayerTypeType) (= (type |xs#0@@14|) DatatypeTypeType)) (or (|_module.__default.Elements#canCall| |xs#0@@14|) (and (not (= 13 $FunctionContextHeight)) ($Is |xs#0@@14| (Tclass._module.List |#$AbInt|))))) ($Is (_module.__default.Elements $ly@@14 |xs#0@@14|) (TSet |#$AbInt|)))
 :qid |SMNADTLi.138:10|
 :skolemid |1046|
 :pattern ( (_module.__default.Elements $ly@@14 |xs#0@@14|))
))))
(assert (forall (($ly@@15 T@U) (|xs#0@@15| T@U) ) (!  (=> (and (and (= (type $ly@@15) LayerTypeType) (= (type |xs#0@@15|) DatatypeTypeType)) ($Is |xs#0@@15| (Tclass._module.List |#$AbInt|))) (and (=> (|_module.__default.Elements#requires| $ly@@15 |xs#0@@15|) true) (=> true (|_module.__default.Elements#requires| $ly@@15 |xs#0@@15|))))
 :qid |SMNADTLi.138:10|
 :skolemid |1047|
 :pattern ( (|_module.__default.Elements#requires| $ly@@15 |xs#0@@15|))
)))
(assert  (=> (<= 13 $FunctionContextHeight) (forall (($ly@@16 T@U) (|xs#0@@16| T@U) ) (!  (=> (and (and (= (type $ly@@16) LayerTypeType) (= (type |xs#0@@16|) DatatypeTypeType)) (or (|_module.__default.Elements#canCall| |xs#0@@16|) (and (not (= 13 $FunctionContextHeight)) ($Is |xs#0@@16| (Tclass._module.List |#$AbInt|))))) (and (=> (not (_module.List.Nil_q |xs#0@@16|)) (let ((|tail#1@@1| (_module.List.tail |xs#0@@16|)))
(|_module.__default.Elements#canCall| |tail#1@@1|))) (= (_module.__default.Elements ($LS $ly@@16) |xs#0@@16|) (ite (_module.List.Nil_q |xs#0@@16|) (|Set#Empty| BoxType) (let ((|tail#0@@1| (_module.List.tail |xs#0@@16|)))
(let ((|x#0@@3| (_module.List.head |xs#0@@16|)))
(|Set#Union| (|Set#UnionOne| (|Set#Empty| BoxType) |x#0@@3|) (_module.__default.Elements $ly@@16 |tail#0@@1|))))))))
 :qid |SMNADTLi.138:10|
 :skolemid |1048|
 :pattern ( (_module.__default.Elements ($LS $ly@@16) |xs#0@@16|))
))))
(assert  (=> (<= 13 $FunctionContextHeight) (forall (($ly@@17 T@U) (|xs#0@@17| T@U) ) (!  (=> (and (and (= (type $ly@@17) LayerTypeType) (= (type |xs#0@@17|) DatatypeTypeType)) (or (|_module.__default.Elements#canCall| (Lit |xs#0@@17|)) (and (not (= 13 $FunctionContextHeight)) ($Is |xs#0@@17| (Tclass._module.List |#$AbInt|))))) (and (=> (not (U_2_bool (Lit (bool_2_U (_module.List.Nil_q (Lit |xs#0@@17|)))))) (let ((|tail#3@@1| (Lit (_module.List.tail (Lit |xs#0@@17|)))))
(|_module.__default.Elements#canCall| |tail#3@@1|))) (= (_module.__default.Elements ($LS $ly@@17) (Lit |xs#0@@17|)) (ite (_module.List.Nil_q (Lit |xs#0@@17|)) (|Set#Empty| BoxType) (let ((|tail#2@@1| (Lit (_module.List.tail (Lit |xs#0@@17|)))))
(let ((|x#2@@0| (Lit (_module.List.head (Lit |xs#0@@17|)))))
(|Set#Union| (|Set#UnionOne| (|Set#Empty| BoxType) |x#2@@0|) (_module.__default.Elements ($LS $ly@@17) |tail#2@@1|))))))))
 :qid |SMNADTLi.138:10|
 :weight 3
 :skolemid |1049|
 :pattern ( (_module.__default.Elements ($LS $ly@@17) (Lit |xs#0@@17|)))
))))
(assert (forall (($ly@@18 T@U) (|xs#0@@18| T@U) ) (!  (=> (and (= (type $ly@@18) LayerTypeType) (= (type |xs#0@@18|) DatatypeTypeType)) (and (=> (_module.__default.NoDuplicates ($LS $ly@@18) |xs#0@@18|) (_module.__default.NoDuplicates $ly@@18 |xs#0@@18|)) (=> (_module.__default.NoDuplicates $ly@@18 |xs#0@@18|) (_module.__default.NoDuplicates ($LS $ly@@18) |xs#0@@18|))))
 :qid |SMNADTLi.154:11|
 :skolemid |1054|
 :pattern ( (_module.__default.NoDuplicates ($LS $ly@@18) |xs#0@@18|))
)))
(assert (forall (($ly@@19 T@U) (|xs#0@@19| T@U) ) (!  (=> (and (= (type $ly@@19) LayerTypeType) (= (type |xs#0@@19|) DatatypeTypeType)) (and (=> (_module.__default.NoDuplicates $ly@@19 |xs#0@@19|) (_module.__default.NoDuplicates $LZ |xs#0@@19|)) (=> (_module.__default.NoDuplicates $LZ |xs#0@@19|) (_module.__default.NoDuplicates $ly@@19 |xs#0@@19|))))
 :qid |SMNADTLi.154:11|
 :skolemid |1055|
 :pattern ( (_module.__default.NoDuplicates (AsFuelBottom $ly@@19) |xs#0@@19|))
)))
(assert  (=> (<= 14 $FunctionContextHeight) (forall (($ly@@20 T@U) (|xs#0@@20| T@U) ) (!  (=> (and (and (= (type $ly@@20) LayerTypeType) (= (type |xs#0@@20|) DatatypeTypeType)) (or (|_module.__default.NoDuplicates#canCall| |xs#0@@20|) (and (not (= 14 $FunctionContextHeight)) ($Is |xs#0@@20| (Tclass._module.List |#$AbInt|))))) true)
 :qid |SMNADTLi.154:11|
 :skolemid |1056|
 :pattern ( (_module.__default.NoDuplicates $ly@@20 |xs#0@@20|))
))))
(assert (forall (($ly@@21 T@U) (|xs#0@@21| T@U) ) (!  (=> (and (and (= (type $ly@@21) LayerTypeType) (= (type |xs#0@@21|) DatatypeTypeType)) ($Is |xs#0@@21| (Tclass._module.List |#$AbInt|))) (and (=> (|_module.__default.NoDuplicates#requires| $ly@@21 |xs#0@@21|) true) (=> true (|_module.__default.NoDuplicates#requires| $ly@@21 |xs#0@@21|))))
 :qid |SMNADTLi.154:11|
 :skolemid |1057|
 :pattern ( (|_module.__default.NoDuplicates#requires| $ly@@21 |xs#0@@21|))
)))
(assert  (=> (<= 14 $FunctionContextHeight) (forall (($ly@@22 T@U) (|xs#0@@22| T@U) ) (!  (=> (and (and (= (type $ly@@22) LayerTypeType) (= (type |xs#0@@22|) DatatypeTypeType)) (or (|_module.__default.NoDuplicates#canCall| |xs#0@@22|) (and (not (= 14 $FunctionContextHeight)) ($Is |xs#0@@22| (Tclass._module.List |#$AbInt|))))) (and (=> (not (_module.List.Nil_q |xs#0@@22|)) (let ((|tail#1@@2| (_module.List.tail |xs#0@@22|)))
(let ((|x#1@@0| (_module.List.head |xs#0@@22|)))
 (and (|_module.__default.Elements#canCall| |tail#1@@2|) (=> (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |tail#1@@2|) |x#1@@0|))) (|_module.__default.NoDuplicates#canCall| |tail#1@@2|)))))) (and (=> (_module.__default.NoDuplicates ($LS $ly@@22) |xs#0@@22|) (ite (_module.List.Nil_q |xs#0@@22|) true (let ((|tail#0@@2| (_module.List.tail |xs#0@@22|)))
(let ((|x#0@@4| (_module.List.head |xs#0@@22|)))
 (and (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |tail#0@@2|) |x#0@@4|))) (_module.__default.NoDuplicates $ly@@22 |tail#0@@2|)))))) (=> (ite (_module.List.Nil_q |xs#0@@22|) true (let ((|tail#0@@3| (_module.List.tail |xs#0@@22|)))
(let ((|x#0@@5| (_module.List.head |xs#0@@22|)))
 (and (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |tail#0@@3|) |x#0@@5|))) (_module.__default.NoDuplicates $ly@@22 |tail#0@@3|))))) (_module.__default.NoDuplicates ($LS $ly@@22) |xs#0@@22|)))))
 :qid |SMNADTLi.154:11|
 :skolemid |1058|
 :pattern ( (_module.__default.NoDuplicates ($LS $ly@@22) |xs#0@@22|))
))))
(assert  (=> (<= 14 $FunctionContextHeight) (forall (($ly@@23 T@U) (|xs#0@@23| T@U) ) (!  (=> (and (and (= (type $ly@@23) LayerTypeType) (= (type |xs#0@@23|) DatatypeTypeType)) (or (|_module.__default.NoDuplicates#canCall| (Lit |xs#0@@23|)) (and (not (= 14 $FunctionContextHeight)) ($Is |xs#0@@23| (Tclass._module.List |#$AbInt|))))) (and (=> (not (U_2_bool (Lit (bool_2_U (_module.List.Nil_q (Lit |xs#0@@23|)))))) (let ((|tail#3@@2| (Lit (_module.List.tail (Lit |xs#0@@23|)))))
(let ((|x#3@@0| (Lit (_module.List.head (Lit |xs#0@@23|)))))
 (and (|_module.__default.Elements#canCall| |tail#3@@2|) (=> (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |tail#3@@2|) |x#3@@0|))) (|_module.__default.NoDuplicates#canCall| |tail#3@@2|)))))) (and (=> (_module.__default.NoDuplicates ($LS $ly@@23) (Lit |xs#0@@23|)) (ite (_module.List.Nil_q (Lit |xs#0@@23|)) true (let ((|tail#2@@2| (Lit (_module.List.tail (Lit |xs#0@@23|)))))
(let ((|x#2@@1| (Lit (_module.List.head (Lit |xs#0@@23|)))))
 (and (not (U_2_bool (MapType0Select (Lit (_module.__default.Elements ($LS $LZ) |tail#2@@2|)) |x#2@@1|))) (_module.__default.NoDuplicates ($LS $ly@@23) |tail#2@@2|)))))) (=> (ite (_module.List.Nil_q (Lit |xs#0@@23|)) true (let ((|tail#2@@3| (Lit (_module.List.tail (Lit |xs#0@@23|)))))
(let ((|x#2@@2| (Lit (_module.List.head (Lit |xs#0@@23|)))))
 (and (not (U_2_bool (MapType0Select (Lit (_module.__default.Elements ($LS $LZ) |tail#2@@3|)) |x#2@@2|))) (_module.__default.NoDuplicates ($LS $ly@@23) |tail#2@@3|))))) (_module.__default.NoDuplicates ($LS $ly@@23) (Lit |xs#0@@23|))))))
 :qid |SMNADTLi.154:11|
 :weight 3
 :skolemid |1059|
 :pattern ( (_module.__default.NoDuplicates ($LS $ly@@23) (Lit |xs#0@@23|)))
))))
(assert (forall ((arg0@@210 T@U) (arg1@@97 T@U) ) (! (= (type (_module.__default.IntRange arg0@@210 arg1@@97)) (MapType0Type BoxType boolType))
 :qid |funType:_module.__default.IntRange|
 :pattern ( (_module.__default.IntRange arg0@@210 arg1@@97))
)))
(assert  (=> (<= 36 $FunctionContextHeight) (forall ((|lo#0@@1| T@U) (|len#0@@1| T@U) ) (!  (=> (and (and (= (type |lo#0@@1|) BoxType) (= (type |len#0@@1|) BoxType)) (or (|_module.__default.IntRange#canCall| |lo#0@@1| |len#0@@1|) (and (not (= 36 $FunctionContextHeight)) (and ($IsBox |lo#0@@1| |#$AbInt|) ($IsBox |len#0@@1| |#$AbInt|))))) (and (= (_module.__default.AbSetLen (_module.__default.IntRange |lo#0@@1| |len#0@@1|)) |len#0@@1|) ($Is (_module.__default.IntRange |lo#0@@1| |len#0@@1|) (TSet |#$AbInt|))))
 :qid |SMNADTLi.193:19|
 :skolemid |1076|
 :pattern ( (_module.__default.IntRange |lo#0@@1| |len#0@@1|))
))))
(assert (forall ((|lo#0@@2| T@U) (|len#0@@2| T@U) ) (!  (=> (and (and (= (type |lo#0@@2|) BoxType) (= (type |len#0@@2|) BoxType)) (and ($IsBox |lo#0@@2| |#$AbInt|) ($IsBox |len#0@@2| |#$AbInt|))) (and (=> (|_module.__default.IntRange#requires| |lo#0@@2| |len#0@@2|) true) (=> true (|_module.__default.IntRange#requires| |lo#0@@2| |len#0@@2|))))
 :qid |SMNADTLi.193:19|
 :skolemid |1077|
 :pattern ( (|_module.__default.IntRange#requires| |lo#0@@2| |len#0@@2|))
)))
(assert  (=> (<= 36 $FunctionContextHeight) (forall ((|lo#0@@3| T@U) (|len#0@@3| T@U) ) (!  (=> (and (and (= (type |lo#0@@3|) BoxType) (= (type |len#0@@3|) BoxType)) (or (|_module.__default.IntRange#canCall| |lo#0@@3| |len#0@@3|) (and (not (= 36 $FunctionContextHeight)) (and ($IsBox |lo#0@@3| |#$AbInt|) ($IsBox |len#0@@3| |#$AbInt|))))) (and (|_module.__default.AbBoundSet#canCall| |lo#0@@3| |len#0@@3|) (= (_module.__default.IntRange |lo#0@@3| |len#0@@3|) (let ((|S#0| (_module.__default.AbBoundSet |lo#0@@3| |len#0@@3|)))
|S#0|))))
 :qid |SMNADTLi.193:19|
 :skolemid |1078|
 :pattern ( (_module.__default.IntRange |lo#0@@3| |len#0@@3|))
))))
(assert  (=> (<= 36 $FunctionContextHeight) (forall ((|lo#0@@4| T@U) (|len#0@@4| T@U) ) (!  (=> (and (and (= (type |lo#0@@4|) BoxType) (= (type |len#0@@4|) BoxType)) (or (|_module.__default.IntRange#canCall| (Lit |lo#0@@4|) (Lit |len#0@@4|)) (and (not (= 36 $FunctionContextHeight)) (and ($IsBox |lo#0@@4| |#$AbInt|) ($IsBox |len#0@@4| |#$AbInt|))))) (and (|_module.__default.AbBoundSet#canCall| (Lit |lo#0@@4|) (Lit |len#0@@4|)) (= (_module.__default.IntRange (Lit |lo#0@@4|) (Lit |len#0@@4|)) (let ((|S#1| (_module.__default.AbBoundSet (Lit |lo#0@@4|) (Lit |len#0@@4|))))
|S#1|))))
 :qid |SMNADTLi.193:19|
 :weight 3
 :skolemid |1079|
 :pattern ( (_module.__default.IntRange (Lit |lo#0@@4|) (Lit |len#0@@4|)))
))))
(assert (forall ((arg0@@211 T@U) ) (! (= (type (_module.__default.SmallestMissingNumber arg0@@211)) BoxType)
 :qid |funType:_module.__default.SmallestMissingNumber|
 :pattern ( (_module.__default.SmallestMissingNumber arg0@@211))
)))
(assert  (=> (<= 34 $FunctionContextHeight) (forall ((|xs#0@@24| T@U) ) (!  (=> (and (= (type |xs#0@@24|) DatatypeTypeType) (or (|_module.__default.SmallestMissingNumber#canCall| |xs#0@@24|) (and (not (= 34 $FunctionContextHeight)) ($Is |xs#0@@24| (Tclass._module.List |#$AbInt|))))) ($IsBox (_module.__default.SmallestMissingNumber |xs#0@@24|) |#$AbInt|))
 :qid |SMNADTLi.203:39|
 :skolemid |1084|
 :pattern ( (_module.__default.SmallestMissingNumber |xs#0@@24|))
))))
(assert (forall ((|xs#0@@25| T@U) ) (!  (=> (and (= (type |xs#0@@25|) DatatypeTypeType) ($Is |xs#0@@25| (Tclass._module.List |#$AbInt|))) (and (=> (|_module.__default.SmallestMissingNumber#requires| |xs#0@@25|) true) (=> true (|_module.__default.SmallestMissingNumber#requires| |xs#0@@25|))))
 :qid |SMNADTLi.203:39|
 :skolemid |1085|
 :pattern ( (|_module.__default.SmallestMissingNumber#requires| |xs#0@@25|))
)))
(assert (forall ((arg0@@212 T@U) (arg1@@98 T@U) (arg2@@47 T@U) (arg3@@25 T@U) ) (! (= (type (_module.__default.SMN arg0@@212 arg1@@98 arg2@@47 arg3@@25)) BoxType)
 :qid |funType:_module.__default.SMN|
 :pattern ( (_module.__default.SMN arg0@@212 arg1@@98 arg2@@47 arg3@@25))
)))
(assert  (=> (<= 34 $FunctionContextHeight) (forall ((|xs#0@@26| T@U) ) (!  (=> (and (= (type |xs#0@@26|) DatatypeTypeType) (or (|_module.__default.SmallestMissingNumber#canCall| |xs#0@@26|) (and (not (= 34 $FunctionContextHeight)) ($Is |xs#0@@26| (Tclass._module.List |#$AbInt|))))) (and (and (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.Length#canCall| |xs#0@@26|)) (|_module.__default.SMN#canCall| |xs#0@@26| (_module.__default.int2adt (LitInt 0)) (_module.__default.Length ($LS $LZ) |xs#0@@26|))) (= (_module.__default.SmallestMissingNumber |xs#0@@26|) (_module.__default.SMN ($LS $LZ) |xs#0@@26| (_module.__default.int2adt (LitInt 0)) (_module.__default.Length ($LS $LZ) |xs#0@@26|)))))
 :qid |SMNADTLi.203:39|
 :skolemid |1086|
 :pattern ( (_module.__default.SmallestMissingNumber |xs#0@@26|))
))))
(assert  (=> (<= 34 $FunctionContextHeight) (forall ((|xs#0@@27| T@U) ) (!  (=> (and (= (type |xs#0@@27|) DatatypeTypeType) (or (|_module.__default.SmallestMissingNumber#canCall| (Lit |xs#0@@27|)) (and (not (= 34 $FunctionContextHeight)) ($Is |xs#0@@27| (Tclass._module.List |#$AbInt|))))) (and (and (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.Length#canCall| (Lit |xs#0@@27|))) (|_module.__default.SMN#canCall| (Lit |xs#0@@27|) (_module.__default.int2adt (LitInt 0)) (Lit (_module.__default.Length ($LS $LZ) (Lit |xs#0@@27|))))) (= (_module.__default.SmallestMissingNumber (Lit |xs#0@@27|)) (_module.__default.SMN ($LS $LZ) (Lit |xs#0@@27|) (_module.__default.int2adt (LitInt 0)) (Lit (_module.__default.Length ($LS $LZ) (Lit |xs#0@@27|)))))))
 :qid |SMNADTLi.203:39|
 :weight 3
 :skolemid |1087|
 :pattern ( (_module.__default.SmallestMissingNumber (Lit |xs#0@@27|)))
))))
(assert (forall (($ly@@24 T@U) (|xs#0@@28| T@U) (|n#0@@19| T@U) (|len#0@@5| T@U) ) (!  (=> (and (and (and (= (type $ly@@24) LayerTypeType) (= (type |xs#0@@28|) DatatypeTypeType)) (= (type |n#0@@19|) BoxType)) (= (type |len#0@@5|) BoxType)) (= (_module.__default.SMN ($LS $ly@@24) |xs#0@@28| |n#0@@19| |len#0@@5|) (_module.__default.SMN $ly@@24 |xs#0@@28| |n#0@@19| |len#0@@5|)))
 :qid |SMNADTLi.208:17|
 :skolemid |1091|
 :pattern ( (_module.__default.SMN ($LS $ly@@24) |xs#0@@28| |n#0@@19| |len#0@@5|))
)))
(assert (forall (($ly@@25 T@U) (|xs#0@@29| T@U) (|n#0@@20| T@U) (|len#0@@6| T@U) ) (!  (=> (and (and (and (= (type $ly@@25) LayerTypeType) (= (type |xs#0@@29|) DatatypeTypeType)) (= (type |n#0@@20|) BoxType)) (= (type |len#0@@6|) BoxType)) (= (_module.__default.SMN $ly@@25 |xs#0@@29| |n#0@@20| |len#0@@6|) (_module.__default.SMN $LZ |xs#0@@29| |n#0@@20| |len#0@@6|)))
 :qid |SMNADTLi.208:17|
 :skolemid |1092|
 :pattern ( (_module.__default.SMN (AsFuelBottom $ly@@25) |xs#0@@29| |n#0@@20| |len#0@@6|))
)))
(assert  (=> (<= 33 $FunctionContextHeight) (forall (($ly@@26 T@U) (|xs#0@@30| T@U) (|n#0@@21| T@U) (|len#0@@7| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@26) LayerTypeType) (= (type |xs#0@@30|) DatatypeTypeType)) (= (type |n#0@@21|) BoxType)) (= (type |len#0@@7|) BoxType)) (or (|_module.__default.SMN#canCall| |xs#0@@30| |n#0@@21| |len#0@@7|) (and (not (= 33 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@30| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@21| |#$AbInt|)) ($IsBox |len#0@@7| |#$AbInt|)) (= |len#0@@7| (_module.__default.Length ($LS $LZ) |xs#0@@30|)))))) ($IsBox (_module.__default.SMN $ly@@26 |xs#0@@30| |n#0@@21| |len#0@@7|) |#$AbInt|))
 :qid |SMNADTLi.208:17|
 :skolemid |1093|
 :pattern ( (_module.__default.SMN $ly@@26 |xs#0@@30| |n#0@@21| |len#0@@7|))
))))
(assert (forall (($ly@@27 T@U) (|xs#0@@31| T@U) (|n#0@@22| T@U) (|len#0@@8| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@27) LayerTypeType) (= (type |xs#0@@31|) DatatypeTypeType)) (= (type |n#0@@22|) BoxType)) (= (type |len#0@@8|) BoxType)) (and (and ($Is |xs#0@@31| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@22| |#$AbInt|)) ($IsBox |len#0@@8| |#$AbInt|))) (and (=> (|_module.__default.SMN#requires| $ly@@27 |xs#0@@31| |n#0@@22| |len#0@@8|) (= |len#0@@8| (_module.__default.Length ($LS $LZ) |xs#0@@31|))) (=> (= |len#0@@8| (_module.__default.Length ($LS $LZ) |xs#0@@31|)) (|_module.__default.SMN#requires| $ly@@27 |xs#0@@31| |n#0@@22| |len#0@@8|))))
 :qid |SMNADTLi.208:17|
 :skolemid |1094|
 :pattern ( (|_module.__default.SMN#requires| $ly@@27 |xs#0@@31| |n#0@@22| |len#0@@8|))
)))
(assert  (=> (<= 33 $FunctionContextHeight) (forall (($ly@@28 T@U) (|xs#0@@32| T@U) (|n#0@@23| T@U) (|len#0@@9| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@28) LayerTypeType) (= (type |xs#0@@32|) DatatypeTypeType)) (= (type |n#0@@23|) BoxType)) (= (type |len#0@@9|) BoxType)) (or (|_module.__default.SMN#canCall| |xs#0@@32| |n#0@@23| |len#0@@9|) (and (not (= 33 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@32| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@23| |#$AbInt|)) ($IsBox |len#0@@9| |#$AbInt|)) (= |len#0@@9| (_module.__default.Length ($LS $LZ) |xs#0@@32|)))))) (and (and (and (and (and (|_module.__default.int2adt#canCall| (LitInt 2)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 2)) |len#0@@9|)) (=> (not (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) |len#0@@9|)) (|_module.__default.int2adt#canCall| (LitInt 2)))) (=> (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) |len#0@@9|) (= (_module.__default.int2adt (LitInt 2)) |len#0@@9|)) (and (and (and (|_module.__default.AbDiv2#canCall| |len#0@@9|) (|_module.__default.AbInc#canCall| |n#0@@23| (_module.__default.AbDiv2 |len#0@@9|))) (|_module.__default.Split#canCall| |xs#0@@32| (_module.__default.AbInc |n#0@@23| (_module.__default.AbDiv2 |len#0@@9|)))) (let ((|R#0@@0| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@32| (_module.__default.AbInc |n#0@@23| (_module.__default.AbDiv2 |len#0@@9|)))))))
(let ((|L#0@@0| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@32| (_module.__default.AbInc |n#0@@23| (_module.__default.AbDiv2 |len#0@@9|)))))))
 (and (|_module.__default.Length#canCall| |L#0@@0|) (let ((|llen#0| (_module.__default.Length ($LS $LZ) |L#0@@0|)))
 (and (and (and (|_module.__default.AbDiv2#canCall| |len#0@@9|) (|_module.__default.AbLt#canCall| |llen#0| (_module.__default.AbDiv2 |len#0@@9|))) (=> (_module.__default.AbLt |llen#0| (_module.__default.AbDiv2 |len#0@@9|)) (|_module.__default.SMN#canCall| |L#0@@0| |n#0@@23| |llen#0|))) (=> (not (_module.__default.AbLt |llen#0| (_module.__default.AbDiv2 |len#0@@9|))) (and (and (|_module.__default.AbInc#canCall| |n#0@@23| |llen#0|) (|_module.__default.AbDec#canCall| |len#0@@9| |llen#0|)) (|_module.__default.SMN#canCall| |R#0@@0| (_module.__default.AbInc |n#0@@23| |llen#0|) (_module.__default.AbDec |len#0@@9| |llen#0|)))))))))))) (=> (not (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) |len#0@@9|) (= (_module.__default.int2adt (LitInt 2)) |len#0@@9|))) (=> (_module.List.Cons_q |xs#0@@32|) (=> (= (_module.List.head |xs#0@@32|) |n#0@@23|) (|_module.__default.AbInc1#canCall| |n#0@@23|))))) (= (_module.__default.SMN ($LS $ly@@28) |xs#0@@32| |n#0@@23| |len#0@@9|) (ite  (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) |len#0@@9|) (= (_module.__default.int2adt (LitInt 2)) |len#0@@9|)) (let ((|R#0@@1| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@32| (_module.__default.AbInc |n#0@@23| (_module.__default.AbDiv2 |len#0@@9|)))))))
(let ((|L#0@@1| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@32| (_module.__default.AbInc |n#0@@23| (_module.__default.AbDiv2 |len#0@@9|)))))))
(let ((|llen#0@@0| (_module.__default.Length ($LS $LZ) |L#0@@1|)))
(ite (_module.__default.AbLt |llen#0@@0| (_module.__default.AbDiv2 |len#0@@9|)) (_module.__default.SMN $ly@@28 |L#0@@1| |n#0@@23| |llen#0@@0|) (_module.__default.SMN $ly@@28 |R#0@@1| (_module.__default.AbInc |n#0@@23| |llen#0@@0|) (_module.__default.AbDec |len#0@@9| |llen#0@@0|)))))) (ite (_module.List.Cons_q |xs#0@@32|) (ite (= (_module.List.head |xs#0@@32|) |n#0@@23|) (_module.__default.AbInc1 |n#0@@23|) |n#0@@23|) |n#0@@23|)))))
 :qid |SMNADTLi.208:17|
 :skolemid |1095|
 :pattern ( (_module.__default.SMN ($LS $ly@@28) |xs#0@@32| |n#0@@23| |len#0@@9|))
))))
(assert  (=> (<= 33 $FunctionContextHeight) (forall (($ly@@29 T@U) (|xs#0@@33| T@U) (|n#0@@24| T@U) (|len#0@@10| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@29) LayerTypeType) (= (type |xs#0@@33|) DatatypeTypeType)) (= (type |n#0@@24|) BoxType)) (= (type |len#0@@10|) BoxType)) (or (|_module.__default.SMN#canCall| |xs#0@@33| |n#0@@24| (Lit |len#0@@10|)) (and (not (= 33 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@33| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@24| |#$AbInt|)) ($IsBox |len#0@@10| |#$AbInt|)) (= (Lit |len#0@@10|) (_module.__default.Length ($LS $LZ) |xs#0@@33|)))))) (and (and (and (and (and (|_module.__default.int2adt#canCall| (LitInt 2)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|))) (=> (not (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|))) (|_module.__default.int2adt#canCall| (LitInt 2)))) (=> (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|)) (= (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|))) (and (and (and (|_module.__default.AbDiv2#canCall| (Lit |len#0@@10|)) (|_module.__default.AbInc#canCall| |n#0@@24| (_module.__default.AbDiv2 (Lit |len#0@@10|)))) (|_module.__default.Split#canCall| |xs#0@@33| (_module.__default.AbInc |n#0@@24| (_module.__default.AbDiv2 (Lit |len#0@@10|))))) (let ((|R#1| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@33| (_module.__default.AbInc |n#0@@24| (_module.__default.AbDiv2 (Lit |len#0@@10|))))))))
(let ((|L#1| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@33| (_module.__default.AbInc |n#0@@24| (_module.__default.AbDiv2 (Lit |len#0@@10|))))))))
 (and (|_module.__default.Length#canCall| |L#1|) (let ((|llen#1| (_module.__default.Length ($LS $LZ) |L#1|)))
 (and (and (and (|_module.__default.AbDiv2#canCall| (Lit |len#0@@10|)) (|_module.__default.AbLt#canCall| |llen#1| (_module.__default.AbDiv2 (Lit |len#0@@10|)))) (=> (_module.__default.AbLt |llen#1| (_module.__default.AbDiv2 (Lit |len#0@@10|))) (|_module.__default.SMN#canCall| |L#1| |n#0@@24| |llen#1|))) (=> (not (_module.__default.AbLt |llen#1| (_module.__default.AbDiv2 (Lit |len#0@@10|)))) (and (and (|_module.__default.AbInc#canCall| |n#0@@24| |llen#1|) (|_module.__default.AbDec#canCall| (Lit |len#0@@10|) |llen#1|)) (|_module.__default.SMN#canCall| |R#1| (_module.__default.AbInc |n#0@@24| |llen#1|) (_module.__default.AbDec (Lit |len#0@@10|) |llen#1|)))))))))))) (=> (not (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|)) (= (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|)))) (=> (_module.List.Cons_q |xs#0@@33|) (=> (= (_module.List.head |xs#0@@33|) |n#0@@24|) (|_module.__default.AbInc1#canCall| |n#0@@24|))))) (= (_module.__default.SMN ($LS $ly@@29) |xs#0@@33| |n#0@@24| (Lit |len#0@@10|)) (ite  (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|)) (= (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@10|))) (let ((|R#1@@0| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@33| (_module.__default.AbInc |n#0@@24| (_module.__default.AbDiv2 (Lit |len#0@@10|))))))))
(let ((|L#1@@0| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@33| (_module.__default.AbInc |n#0@@24| (_module.__default.AbDiv2 (Lit |len#0@@10|))))))))
(let ((|llen#1@@0| (_module.__default.Length ($LS $LZ) |L#1@@0|)))
(ite (_module.__default.AbLt |llen#1@@0| (_module.__default.AbDiv2 (Lit |len#0@@10|))) (_module.__default.SMN ($LS $ly@@29) |L#1@@0| |n#0@@24| |llen#1@@0|) (_module.__default.SMN ($LS $ly@@29) |R#1@@0| (_module.__default.AbInc |n#0@@24| |llen#1@@0|) (_module.__default.AbDec (Lit |len#0@@10|) |llen#1@@0|)))))) (ite (_module.List.Cons_q |xs#0@@33|) (ite (= (_module.List.head |xs#0@@33|) |n#0@@24|) (_module.__default.AbInc1 |n#0@@24|) |n#0@@24|) |n#0@@24|)))))
 :qid |SMNADTLi.208:17|
 :weight 3
 :skolemid |1096|
 :pattern ( (_module.__default.SMN ($LS $ly@@29) |xs#0@@33| |n#0@@24| (Lit |len#0@@10|)))
))))
(assert  (=> (<= 33 $FunctionContextHeight) (forall (($ly@@30 T@U) (|xs#0@@34| T@U) (|n#0@@25| T@U) (|len#0@@11| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@30) LayerTypeType) (= (type |xs#0@@34|) DatatypeTypeType)) (= (type |n#0@@25|) BoxType)) (= (type |len#0@@11|) BoxType)) (or (|_module.__default.SMN#canCall| (Lit |xs#0@@34|) (Lit |n#0@@25|) (Lit |len#0@@11|)) (and (not (= 33 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@34| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@25| |#$AbInt|)) ($IsBox |len#0@@11| |#$AbInt|)) (= (Lit |len#0@@11|) (Lit (_module.__default.Length ($LS $LZ) (Lit |xs#0@@34|)))))))) (and (and (and (and (and (|_module.__default.int2adt#canCall| (LitInt 2)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|))) (=> (not (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|))) (|_module.__default.int2adt#canCall| (LitInt 2)))) (=> (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|)) (= (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|))) (and (and (and (|_module.__default.AbDiv2#canCall| (Lit |len#0@@11|)) (|_module.__default.AbInc#canCall| (Lit |n#0@@25|) (_module.__default.AbDiv2 (Lit |len#0@@11|)))) (|_module.__default.Split#canCall| (Lit |xs#0@@34|) (_module.__default.AbInc (Lit |n#0@@25|) (_module.__default.AbDiv2 (Lit |len#0@@11|))))) (let ((|R#2@@0| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@34|) (_module.__default.AbInc (Lit |n#0@@25|) (_module.__default.AbDiv2 (Lit |len#0@@11|))))))))
(let ((|L#2@@0| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@34|) (_module.__default.AbInc (Lit |n#0@@25|) (_module.__default.AbDiv2 (Lit |len#0@@11|))))))))
 (and (|_module.__default.Length#canCall| |L#2@@0|) (let ((|llen#2| (_module.__default.Length ($LS $LZ) |L#2@@0|)))
 (and (and (and (|_module.__default.AbDiv2#canCall| (Lit |len#0@@11|)) (|_module.__default.AbLt#canCall| |llen#2| (_module.__default.AbDiv2 (Lit |len#0@@11|)))) (=> (_module.__default.AbLt |llen#2| (_module.__default.AbDiv2 (Lit |len#0@@11|))) (|_module.__default.SMN#canCall| |L#2@@0| (Lit |n#0@@25|) |llen#2|))) (=> (not (_module.__default.AbLt |llen#2| (_module.__default.AbDiv2 (Lit |len#0@@11|)))) (and (and (|_module.__default.AbInc#canCall| (Lit |n#0@@25|) |llen#2|) (|_module.__default.AbDec#canCall| (Lit |len#0@@11|) |llen#2|)) (|_module.__default.SMN#canCall| |R#2@@0| (_module.__default.AbInc (Lit |n#0@@25|) |llen#2|) (_module.__default.AbDec (Lit |len#0@@11|) |llen#2|)))))))))))) (=> (not (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|)) (= (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|)))) (=> (U_2_bool (Lit (bool_2_U (_module.List.Cons_q (Lit |xs#0@@34|))))) (=> (= (Lit (_module.List.head (Lit |xs#0@@34|))) (Lit |n#0@@25|)) (|_module.__default.AbInc1#canCall| (Lit |n#0@@25|)))))) (= (_module.__default.SMN ($LS $ly@@30) (Lit |xs#0@@34|) (Lit |n#0@@25|) (Lit |len#0@@11|)) (ite  (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|)) (= (_module.__default.int2adt (LitInt 2)) (Lit |len#0@@11|))) (let ((|R#2@@1| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@34|) (_module.__default.AbInc (Lit |n#0@@25|) (_module.__default.AbDiv2 (Lit |len#0@@11|))))))))
(let ((|L#2@@1| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@34|) (_module.__default.AbInc (Lit |n#0@@25|) (_module.__default.AbDiv2 (Lit |len#0@@11|))))))))
(let ((|llen#2@@0| (_module.__default.Length ($LS $LZ) |L#2@@1|)))
(ite (_module.__default.AbLt |llen#2@@0| (_module.__default.AbDiv2 (Lit |len#0@@11|))) (_module.__default.SMN ($LS $ly@@30) |L#2@@1| (Lit |n#0@@25|) |llen#2@@0|) (_module.__default.SMN ($LS $ly@@30) |R#2@@1| (_module.__default.AbInc (Lit |n#0@@25|) |llen#2@@0|) (_module.__default.AbDec (Lit |len#0@@11|) |llen#2@@0|)))))) (ite (_module.List.Cons_q (Lit |xs#0@@34|)) (ite (= (Lit (_module.List.head (Lit |xs#0@@34|))) (Lit |n#0@@25|)) (_module.__default.AbInc1 (Lit |n#0@@25|)) |n#0@@25|) |n#0@@25|)))))
 :qid |SMNADTLi.208:17|
 :weight 3
 :skolemid |1097|
 :pattern ( (_module.__default.SMN ($LS $ly@@30) (Lit |xs#0@@34|) (Lit |n#0@@25|) (Lit |len#0@@11|)))
))))
(assert (forall ((arg0@@213 T@U) (arg1@@99 T@U) (arg2@@48 T@U) (arg3@@26 T@U) ) (! (= (type (_module.__default.SMN_k arg0@@213 arg1@@99 arg2@@48 arg3@@26)) BoxType)
 :qid |funType:_module.__default.SMN_k|
 :pattern ( (_module.__default.SMN_k arg0@@213 arg1@@99 arg2@@48 arg3@@26))
)))
(assert (forall (($ly@@31 T@U) (|xs#0@@35| T@U) (|n#0@@26| T@U) (|len#0@@12| T@U) ) (!  (=> (and (and (and (= (type $ly@@31) LayerTypeType) (= (type |xs#0@@35|) DatatypeTypeType)) (= (type |n#0@@26|) BoxType)) (= (type |len#0@@12|) BoxType)) (= (_module.__default.SMN_k ($LS $ly@@31) |xs#0@@35| |n#0@@26| |len#0@@12|) (_module.__default.SMN_k $ly@@31 |xs#0@@35| |n#0@@26| |len#0@@12|)))
 :qid |SMNADTLi.325:17|
 :skolemid |1170|
 :pattern ( (_module.__default.SMN_k ($LS $ly@@31) |xs#0@@35| |n#0@@26| |len#0@@12|))
)))
(assert (forall (($ly@@32 T@U) (|xs#0@@36| T@U) (|n#0@@27| T@U) (|len#0@@13| T@U) ) (!  (=> (and (and (and (= (type $ly@@32) LayerTypeType) (= (type |xs#0@@36|) DatatypeTypeType)) (= (type |n#0@@27|) BoxType)) (= (type |len#0@@13|) BoxType)) (= (_module.__default.SMN_k $ly@@32 |xs#0@@36| |n#0@@27| |len#0@@13|) (_module.__default.SMN_k $LZ |xs#0@@36| |n#0@@27| |len#0@@13|)))
 :qid |SMNADTLi.325:17|
 :skolemid |1171|
 :pattern ( (_module.__default.SMN_k (AsFuelBottom $ly@@32) |xs#0@@36| |n#0@@27| |len#0@@13|))
)))
(assert  (=> (<= 48 $FunctionContextHeight) (forall (($ly@@33 T@U) (|xs#0@@37| T@U) (|n#0@@28| T@U) (|len#0@@14| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@33) LayerTypeType) (= (type |xs#0@@37|) DatatypeTypeType)) (= (type |n#0@@28|) BoxType)) (= (type |len#0@@14|) BoxType)) (or (|_module.__default.SMN_k#canCall| |xs#0@@37| |n#0@@28| |len#0@@14|) (and (not (= 48 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@37| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@28| |#$AbInt|)) ($IsBox |len#0@@14| |#$AbInt|)) (= |len#0@@14| (_module.__default.Length ($LS $LZ) |xs#0@@37|)))))) ($IsBox (_module.__default.SMN_k $ly@@33 |xs#0@@37| |n#0@@28| |len#0@@14|) |#$AbInt|))
 :qid |SMNADTLi.325:17|
 :skolemid |1172|
 :pattern ( (_module.__default.SMN_k $ly@@33 |xs#0@@37| |n#0@@28| |len#0@@14|))
))))
(assert (forall (($ly@@34 T@U) (|xs#0@@38| T@U) (|n#0@@29| T@U) (|len#0@@15| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@34) LayerTypeType) (= (type |xs#0@@38|) DatatypeTypeType)) (= (type |n#0@@29|) BoxType)) (= (type |len#0@@15|) BoxType)) (and (and ($Is |xs#0@@38| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@29| |#$AbInt|)) ($IsBox |len#0@@15| |#$AbInt|))) (and (=> (|_module.__default.SMN_k#requires| $ly@@34 |xs#0@@38| |n#0@@29| |len#0@@15|) (= |len#0@@15| (_module.__default.Length ($LS $LZ) |xs#0@@38|))) (=> (= |len#0@@15| (_module.__default.Length ($LS $LZ) |xs#0@@38|)) (|_module.__default.SMN_k#requires| $ly@@34 |xs#0@@38| |n#0@@29| |len#0@@15|))))
 :qid |SMNADTLi.325:17|
 :skolemid |1173|
 :pattern ( (|_module.__default.SMN_k#requires| $ly@@34 |xs#0@@38| |n#0@@29| |len#0@@15|))
)))
(assert  (=> (<= 48 $FunctionContextHeight) (forall (($ly@@35 T@U) (|xs#0@@39| T@U) (|n#0@@30| T@U) (|len#0@@16| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@35) LayerTypeType) (= (type |xs#0@@39|) DatatypeTypeType)) (= (type |n#0@@30|) BoxType)) (= (type |len#0@@16|) BoxType)) (or (|_module.__default.SMN_k#canCall| |xs#0@@39| |n#0@@30| |len#0@@16|) (and (not (= 48 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@39| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@30| |#$AbInt|)) ($IsBox |len#0@@16| |#$AbInt|)) (= |len#0@@16| (_module.__default.Length ($LS $LZ) |xs#0@@39|)))))) (and (and (|$IsA#_module.List| |xs#0@@39|) (=> (not (|_module.List#Equal| |xs#0@@39| |#_module.List.Nil|)) (and (and (|_module.__default.AbInc1#canCall| |len#0@@16|) (|_module.__default.AbDiv2#canCall| (_module.__default.AbInc1 |len#0@@16|))) (let ((|half#0| (_module.__default.AbDiv2 (_module.__default.AbInc1 |len#0@@16|))))
 (and (and (|_module.__default.AbInc#canCall| |n#0@@30| |half#0|) (|_module.__default.Split#canCall| |xs#0@@39| (_module.__default.AbInc |n#0@@30| |half#0|))) (let ((|R#0@@2| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@39| (_module.__default.AbInc |n#0@@30| |half#0|))))))
(let ((|L#0@@2| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@39| (_module.__default.AbInc |n#0@@30| |half#0|))))))
 (and (|_module.__default.Length#canCall| |L#0@@2|) (let ((|llen#0@@1| (_module.__default.Length ($LS $LZ) |L#0@@2|)))
 (and (and (|_module.__default.AbLt#canCall| |llen#0@@1| |half#0|) (=> (_module.__default.AbLt |llen#0@@1| |half#0|) (|_module.__default.SMN_k#canCall| |L#0@@2| |n#0@@30| |llen#0@@1|))) (=> (not (_module.__default.AbLt |llen#0@@1| |half#0|)) (and (and (|_module.__default.AbInc#canCall| |n#0@@30| |llen#0@@1|) (|_module.__default.AbDec#canCall| |len#0@@16| |llen#0@@1|)) (|_module.__default.SMN_k#canCall| |R#0@@2| (_module.__default.AbInc |n#0@@30| |llen#0@@1|) (_module.__default.AbDec |len#0@@16| |llen#0@@1|)))))))))))))) (= (_module.__default.SMN_k ($LS $ly@@35) |xs#0@@39| |n#0@@30| |len#0@@16|) (ite (|_module.List#Equal| |xs#0@@39| |#_module.List.Nil|) |n#0@@30| (let ((|half#0@@0| (_module.__default.AbDiv2 (_module.__default.AbInc1 |len#0@@16|))))
(let ((|R#0@@3| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@39| (_module.__default.AbInc |n#0@@30| |half#0@@0|))))))
(let ((|L#0@@3| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@39| (_module.__default.AbInc |n#0@@30| |half#0@@0|))))))
(let ((|llen#0@@2| (_module.__default.Length ($LS $LZ) |L#0@@3|)))
(ite (_module.__default.AbLt |llen#0@@2| |half#0@@0|) (_module.__default.SMN_k $ly@@35 |L#0@@3| |n#0@@30| |llen#0@@2|) (_module.__default.SMN_k $ly@@35 |R#0@@3| (_module.__default.AbInc |n#0@@30| |llen#0@@2|) (_module.__default.AbDec |len#0@@16| |llen#0@@2|)))))))))))
 :qid |SMNADTLi.325:17|
 :skolemid |1174|
 :pattern ( (_module.__default.SMN_k ($LS $ly@@35) |xs#0@@39| |n#0@@30| |len#0@@16|))
))))
(assert  (=> (<= 48 $FunctionContextHeight) (forall (($ly@@36 T@U) (|xs#0@@40| T@U) (|n#0@@31| T@U) (|len#0@@17| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@36) LayerTypeType) (= (type |xs#0@@40|) DatatypeTypeType)) (= (type |n#0@@31|) BoxType)) (= (type |len#0@@17|) BoxType)) (or (|_module.__default.SMN_k#canCall| |xs#0@@40| |n#0@@31| (Lit |len#0@@17|)) (and (not (= 48 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@40| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@31| |#$AbInt|)) ($IsBox |len#0@@17| |#$AbInt|)) (= (Lit |len#0@@17|) (_module.__default.Length ($LS $LZ) |xs#0@@40|)))))) (and (and (|$IsA#_module.List| |xs#0@@40|) (=> (not (|_module.List#Equal| |xs#0@@40| |#_module.List.Nil|)) (and (and (|_module.__default.AbInc1#canCall| (Lit |len#0@@17|)) (|_module.__default.AbDiv2#canCall| (_module.__default.AbInc1 (Lit |len#0@@17|)))) (let ((|half#1| (_module.__default.AbDiv2 (_module.__default.AbInc1 (Lit |len#0@@17|)))))
 (and (and (|_module.__default.AbInc#canCall| |n#0@@31| |half#1|) (|_module.__default.Split#canCall| |xs#0@@40| (_module.__default.AbInc |n#0@@31| |half#1|))) (let ((|R#1@@1| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@40| (_module.__default.AbInc |n#0@@31| |half#1|))))))
(let ((|L#1@@1| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@40| (_module.__default.AbInc |n#0@@31| |half#1|))))))
 (and (|_module.__default.Length#canCall| |L#1@@1|) (let ((|llen#1@@1| (_module.__default.Length ($LS $LZ) |L#1@@1|)))
 (and (and (|_module.__default.AbLt#canCall| |llen#1@@1| |half#1|) (=> (_module.__default.AbLt |llen#1@@1| |half#1|) (|_module.__default.SMN_k#canCall| |L#1@@1| |n#0@@31| |llen#1@@1|))) (=> (not (_module.__default.AbLt |llen#1@@1| |half#1|)) (and (and (|_module.__default.AbInc#canCall| |n#0@@31| |llen#1@@1|) (|_module.__default.AbDec#canCall| (Lit |len#0@@17|) |llen#1@@1|)) (|_module.__default.SMN_k#canCall| |R#1@@1| (_module.__default.AbInc |n#0@@31| |llen#1@@1|) (_module.__default.AbDec (Lit |len#0@@17|) |llen#1@@1|)))))))))))))) (= (_module.__default.SMN_k ($LS $ly@@36) |xs#0@@40| |n#0@@31| (Lit |len#0@@17|)) (ite (|_module.List#Equal| |xs#0@@40| |#_module.List.Nil|) |n#0@@31| (let ((|half#1@@0| (_module.__default.AbDiv2 (_module.__default.AbInc1 (Lit |len#0@@17|)))))
(let ((|R#1@@2| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@40| (_module.__default.AbInc |n#0@@31| |half#1@@0|))))))
(let ((|L#1@@2| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@40| (_module.__default.AbInc |n#0@@31| |half#1@@0|))))))
(let ((|llen#1@@2| (_module.__default.Length ($LS $LZ) |L#1@@2|)))
(ite (_module.__default.AbLt |llen#1@@2| |half#1@@0|) (_module.__default.SMN_k ($LS $ly@@36) |L#1@@2| |n#0@@31| |llen#1@@2|) (_module.__default.SMN_k ($LS $ly@@36) |R#1@@2| (_module.__default.AbInc |n#0@@31| |llen#1@@2|) (_module.__default.AbDec (Lit |len#0@@17|) |llen#1@@2|)))))))))))
 :qid |SMNADTLi.325:17|
 :weight 3
 :skolemid |1175|
 :pattern ( (_module.__default.SMN_k ($LS $ly@@36) |xs#0@@40| |n#0@@31| (Lit |len#0@@17|)))
))))
(assert  (=> (<= 48 $FunctionContextHeight) (forall (($ly@@37 T@U) (|xs#0@@41| T@U) (|n#0@@32| T@U) (|len#0@@18| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@37) LayerTypeType) (= (type |xs#0@@41|) DatatypeTypeType)) (= (type |n#0@@32|) BoxType)) (= (type |len#0@@18|) BoxType)) (or (|_module.__default.SMN_k#canCall| (Lit |xs#0@@41|) (Lit |n#0@@32|) (Lit |len#0@@18|)) (and (not (= 48 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@41| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@32| |#$AbInt|)) ($IsBox |len#0@@18| |#$AbInt|)) (= (Lit |len#0@@18|) (Lit (_module.__default.Length ($LS $LZ) (Lit |xs#0@@41|)))))))) (and (and (|$IsA#_module.List| (Lit |xs#0@@41|)) (=> (not (|_module.List#Equal| |xs#0@@41| |#_module.List.Nil|)) (and (and (|_module.__default.AbInc1#canCall| (Lit |len#0@@18|)) (|_module.__default.AbDiv2#canCall| (_module.__default.AbInc1 (Lit |len#0@@18|)))) (let ((|half#2| (_module.__default.AbDiv2 (_module.__default.AbInc1 (Lit |len#0@@18|)))))
 (and (and (|_module.__default.AbInc#canCall| (Lit |n#0@@32|) |half#2|) (|_module.__default.Split#canCall| (Lit |xs#0@@41|) (_module.__default.AbInc (Lit |n#0@@32|) |half#2|))) (let ((|R#2@@2| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@41|) (_module.__default.AbInc (Lit |n#0@@32|) |half#2|))))))
(let ((|L#2@@2| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@41|) (_module.__default.AbInc (Lit |n#0@@32|) |half#2|))))))
 (and (|_module.__default.Length#canCall| |L#2@@2|) (let ((|llen#2@@1| (_module.__default.Length ($LS $LZ) |L#2@@2|)))
 (and (and (|_module.__default.AbLt#canCall| |llen#2@@1| |half#2|) (=> (_module.__default.AbLt |llen#2@@1| |half#2|) (|_module.__default.SMN_k#canCall| |L#2@@2| (Lit |n#0@@32|) |llen#2@@1|))) (=> (not (_module.__default.AbLt |llen#2@@1| |half#2|)) (and (and (|_module.__default.AbInc#canCall| (Lit |n#0@@32|) |llen#2@@1|) (|_module.__default.AbDec#canCall| (Lit |len#0@@18|) |llen#2@@1|)) (|_module.__default.SMN_k#canCall| |R#2@@2| (_module.__default.AbInc (Lit |n#0@@32|) |llen#2@@1|) (_module.__default.AbDec (Lit |len#0@@18|) |llen#2@@1|)))))))))))))) (= (_module.__default.SMN_k ($LS $ly@@37) (Lit |xs#0@@41|) (Lit |n#0@@32|) (Lit |len#0@@18|)) (ite (|_module.List#Equal| |xs#0@@41| |#_module.List.Nil|) |n#0@@32| (let ((|half#2@@0| (_module.__default.AbDiv2 (_module.__default.AbInc1 (Lit |len#0@@18|)))))
(let ((|R#2@@3| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@41|) (_module.__default.AbInc (Lit |n#0@@32|) |half#2@@0|))))))
(let ((|L#2@@3| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@41|) (_module.__default.AbInc (Lit |n#0@@32|) |half#2@@0|))))))
(let ((|llen#2@@2| (_module.__default.Length ($LS $LZ) |L#2@@3|)))
(ite (_module.__default.AbLt |llen#2@@2| |half#2@@0|) (_module.__default.SMN_k ($LS $ly@@37) |L#2@@3| (Lit |n#0@@32|) |llen#2@@2|) (_module.__default.SMN_k ($LS $ly@@37) |R#2@@3| (_module.__default.AbInc (Lit |n#0@@32|) |llen#2@@2|) (_module.__default.AbDec (Lit |len#0@@18|) |llen#2@@2|)))))))))))
 :qid |SMNADTLi.325:17|
 :weight 3
 :skolemid |1176|
 :pattern ( (_module.__default.SMN_k ($LS $ly@@37) (Lit |xs#0@@41|) (Lit |n#0@@32|) (Lit |len#0@@18|)))
))))
(assert (forall ((arg0@@214 T@U) (arg1@@100 T@U) (arg2@@49 T@U) (arg3@@27 T@U) ) (! (= (type (_module.__default.SMN_k_k arg0@@214 arg1@@100 arg2@@49 arg3@@27)) BoxType)
 :qid |funType:_module.__default.SMN_k_k|
 :pattern ( (_module.__default.SMN_k_k arg0@@214 arg1@@100 arg2@@49 arg3@@27))
)))
(assert (forall (($ly@@38 T@U) (|xs#0@@42| T@U) (|n#0@@33| T@U) (|len#0@@19| T@U) ) (!  (=> (and (and (and (= (type $ly@@38) LayerTypeType) (= (type |xs#0@@42|) DatatypeTypeType)) (= (type |n#0@@33|) BoxType)) (= (type |len#0@@19|) BoxType)) (= (_module.__default.SMN_k_k ($LS $ly@@38) |xs#0@@42| |n#0@@33| |len#0@@19|) (_module.__default.SMN_k_k $ly@@38 |xs#0@@42| |n#0@@33| |len#0@@19|)))
 :qid |SMNADTLi.419:17|
 :skolemid |1228|
 :pattern ( (_module.__default.SMN_k_k ($LS $ly@@38) |xs#0@@42| |n#0@@33| |len#0@@19|))
)))
(assert (forall (($ly@@39 T@U) (|xs#0@@43| T@U) (|n#0@@34| T@U) (|len#0@@20| T@U) ) (!  (=> (and (and (and (= (type $ly@@39) LayerTypeType) (= (type |xs#0@@43|) DatatypeTypeType)) (= (type |n#0@@34|) BoxType)) (= (type |len#0@@20|) BoxType)) (= (_module.__default.SMN_k_k $ly@@39 |xs#0@@43| |n#0@@34| |len#0@@20|) (_module.__default.SMN_k_k $LZ |xs#0@@43| |n#0@@34| |len#0@@20|)))
 :qid |SMNADTLi.419:17|
 :skolemid |1229|
 :pattern ( (_module.__default.SMN_k_k (AsFuelBottom $ly@@39) |xs#0@@43| |n#0@@34| |len#0@@20|))
)))
(assert  (=> (<= 52 $FunctionContextHeight) (forall (($ly@@40 T@U) (|xs#0@@44| T@U) (|n#0@@35| T@U) (|len#0@@21| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@40) LayerTypeType) (= (type |xs#0@@44|) DatatypeTypeType)) (= (type |n#0@@35|) BoxType)) (= (type |len#0@@21|) BoxType)) (or (|_module.__default.SMN_k_k#canCall| |xs#0@@44| |n#0@@35| |len#0@@21|) (and (not (= 52 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@44| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@35| |#$AbInt|)) ($IsBox |len#0@@21| |#$AbInt|)) (= |len#0@@21| (_module.__default.Length ($LS $LZ) |xs#0@@44|)))))) ($IsBox (_module.__default.SMN_k_k $ly@@40 |xs#0@@44| |n#0@@35| |len#0@@21|) |#$AbInt|))
 :qid |SMNADTLi.419:17|
 :skolemid |1230|
 :pattern ( (_module.__default.SMN_k_k $ly@@40 |xs#0@@44| |n#0@@35| |len#0@@21|))
))))
(assert (forall (($ly@@41 T@U) (|xs#0@@45| T@U) (|n#0@@36| T@U) (|len#0@@22| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@41) LayerTypeType) (= (type |xs#0@@45|) DatatypeTypeType)) (= (type |n#0@@36|) BoxType)) (= (type |len#0@@22|) BoxType)) (and (and ($Is |xs#0@@45| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@36| |#$AbInt|)) ($IsBox |len#0@@22| |#$AbInt|))) (and (=> (|_module.__default.SMN_k_k#requires| $ly@@41 |xs#0@@45| |n#0@@36| |len#0@@22|) (= |len#0@@22| (_module.__default.Length ($LS $LZ) |xs#0@@45|))) (=> (= |len#0@@22| (_module.__default.Length ($LS $LZ) |xs#0@@45|)) (|_module.__default.SMN_k_k#requires| $ly@@41 |xs#0@@45| |n#0@@36| |len#0@@22|))))
 :qid |SMNADTLi.419:17|
 :skolemid |1231|
 :pattern ( (|_module.__default.SMN_k_k#requires| $ly@@41 |xs#0@@45| |n#0@@36| |len#0@@22|))
)))
(assert  (=> (<= 52 $FunctionContextHeight) (forall (($ly@@42 T@U) (|xs#0@@46| T@U) (|n#0@@37| T@U) (|len#0@@23| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@42) LayerTypeType) (= (type |xs#0@@46|) DatatypeTypeType)) (= (type |n#0@@37|) BoxType)) (= (type |len#0@@23|) BoxType)) (or (|_module.__default.SMN_k_k#canCall| |xs#0@@46| |n#0@@37| |len#0@@23|) (and (not (= 52 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@46| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@37| |#$AbInt|)) ($IsBox |len#0@@23| |#$AbInt|)) (= |len#0@@23| (_module.__default.Length ($LS $LZ) |xs#0@@46|)))))) (and (and (|$IsA#_module.List| |xs#0@@46|) (=> (not (|_module.List#Equal| |xs#0@@46| |#_module.List.Nil|)) (and (and (|_module.__default.AbDiv2#canCall| |len#0@@23|) (|_module.__default.AbInc1#canCall| (_module.__default.AbDiv2 |len#0@@23|))) (let ((|half#0@@1| (_module.__default.AbInc1 (_module.__default.AbDiv2 |len#0@@23|))))
 (and (and (|_module.__default.AbInc#canCall| |n#0@@37| |half#0@@1|) (|_module.__default.Split#canCall| |xs#0@@46| (_module.__default.AbInc |n#0@@37| |half#0@@1|))) (let ((|R#0@@4| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@46| (_module.__default.AbInc |n#0@@37| |half#0@@1|))))))
(let ((|L#0@@4| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@46| (_module.__default.AbInc |n#0@@37| |half#0@@1|))))))
 (and (|_module.__default.Length#canCall| |L#0@@4|) (let ((|llen#0@@3| (_module.__default.Length ($LS $LZ) |L#0@@4|)))
 (and (and (|_module.__default.AbLt#canCall| |llen#0@@3| |half#0@@1|) (=> (_module.__default.AbLt |llen#0@@3| |half#0@@1|) (|_module.__default.SMN_k_k#canCall| |L#0@@4| |n#0@@37| |llen#0@@3|))) (=> (not (_module.__default.AbLt |llen#0@@3| |half#0@@1|)) (and (and (|_module.__default.AbInc#canCall| |n#0@@37| |llen#0@@3|) (|_module.__default.AbDec#canCall| |len#0@@23| |llen#0@@3|)) (|_module.__default.SMN_k_k#canCall| |R#0@@4| (_module.__default.AbInc |n#0@@37| |llen#0@@3|) (_module.__default.AbDec |len#0@@23| |llen#0@@3|)))))))))))))) (= (_module.__default.SMN_k_k ($LS $ly@@42) |xs#0@@46| |n#0@@37| |len#0@@23|) (ite (|_module.List#Equal| |xs#0@@46| |#_module.List.Nil|) |n#0@@37| (let ((|half#0@@2| (_module.__default.AbInc1 (_module.__default.AbDiv2 |len#0@@23|))))
(let ((|R#0@@5| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@46| (_module.__default.AbInc |n#0@@37| |half#0@@2|))))))
(let ((|L#0@@5| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@46| (_module.__default.AbInc |n#0@@37| |half#0@@2|))))))
(let ((|llen#0@@4| (_module.__default.Length ($LS $LZ) |L#0@@5|)))
(ite (_module.__default.AbLt |llen#0@@4| |half#0@@2|) (_module.__default.SMN_k_k $ly@@42 |L#0@@5| |n#0@@37| |llen#0@@4|) (_module.__default.SMN_k_k $ly@@42 |R#0@@5| (_module.__default.AbInc |n#0@@37| |llen#0@@4|) (_module.__default.AbDec |len#0@@23| |llen#0@@4|)))))))))))
 :qid |SMNADTLi.419:17|
 :skolemid |1232|
 :pattern ( (_module.__default.SMN_k_k ($LS $ly@@42) |xs#0@@46| |n#0@@37| |len#0@@23|))
))))
(assert  (=> (<= 52 $FunctionContextHeight) (forall (($ly@@43 T@U) (|xs#0@@47| T@U) (|n#0@@38| T@U) (|len#0@@24| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@43) LayerTypeType) (= (type |xs#0@@47|) DatatypeTypeType)) (= (type |n#0@@38|) BoxType)) (= (type |len#0@@24|) BoxType)) (or (|_module.__default.SMN_k_k#canCall| |xs#0@@47| |n#0@@38| (Lit |len#0@@24|)) (and (not (= 52 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@47| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@38| |#$AbInt|)) ($IsBox |len#0@@24| |#$AbInt|)) (= (Lit |len#0@@24|) (_module.__default.Length ($LS $LZ) |xs#0@@47|)))))) (and (and (|$IsA#_module.List| |xs#0@@47|) (=> (not (|_module.List#Equal| |xs#0@@47| |#_module.List.Nil|)) (and (and (|_module.__default.AbDiv2#canCall| (Lit |len#0@@24|)) (|_module.__default.AbInc1#canCall| (_module.__default.AbDiv2 (Lit |len#0@@24|)))) (let ((|half#1@@1| (_module.__default.AbInc1 (_module.__default.AbDiv2 (Lit |len#0@@24|)))))
 (and (and (|_module.__default.AbInc#canCall| |n#0@@38| |half#1@@1|) (|_module.__default.Split#canCall| |xs#0@@47| (_module.__default.AbInc |n#0@@38| |half#1@@1|))) (let ((|R#1@@3| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@47| (_module.__default.AbInc |n#0@@38| |half#1@@1|))))))
(let ((|L#1@@3| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@47| (_module.__default.AbInc |n#0@@38| |half#1@@1|))))))
 (and (|_module.__default.Length#canCall| |L#1@@3|) (let ((|llen#1@@3| (_module.__default.Length ($LS $LZ) |L#1@@3|)))
 (and (and (|_module.__default.AbLt#canCall| |llen#1@@3| |half#1@@1|) (=> (_module.__default.AbLt |llen#1@@3| |half#1@@1|) (|_module.__default.SMN_k_k#canCall| |L#1@@3| |n#0@@38| |llen#1@@3|))) (=> (not (_module.__default.AbLt |llen#1@@3| |half#1@@1|)) (and (and (|_module.__default.AbInc#canCall| |n#0@@38| |llen#1@@3|) (|_module.__default.AbDec#canCall| (Lit |len#0@@24|) |llen#1@@3|)) (|_module.__default.SMN_k_k#canCall| |R#1@@3| (_module.__default.AbInc |n#0@@38| |llen#1@@3|) (_module.__default.AbDec (Lit |len#0@@24|) |llen#1@@3|)))))))))))))) (= (_module.__default.SMN_k_k ($LS $ly@@43) |xs#0@@47| |n#0@@38| (Lit |len#0@@24|)) (ite (|_module.List#Equal| |xs#0@@47| |#_module.List.Nil|) |n#0@@38| (let ((|half#1@@2| (_module.__default.AbInc1 (_module.__default.AbDiv2 (Lit |len#0@@24|)))))
(let ((|R#1@@4| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) |xs#0@@47| (_module.__default.AbInc |n#0@@38| |half#1@@2|))))))
(let ((|L#1@@4| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) |xs#0@@47| (_module.__default.AbInc |n#0@@38| |half#1@@2|))))))
(let ((|llen#1@@4| (_module.__default.Length ($LS $LZ) |L#1@@4|)))
(ite (_module.__default.AbLt |llen#1@@4| |half#1@@2|) (_module.__default.SMN_k_k ($LS $ly@@43) |L#1@@4| |n#0@@38| |llen#1@@4|) (_module.__default.SMN_k_k ($LS $ly@@43) |R#1@@4| (_module.__default.AbInc |n#0@@38| |llen#1@@4|) (_module.__default.AbDec (Lit |len#0@@24|) |llen#1@@4|)))))))))))
 :qid |SMNADTLi.419:17|
 :weight 3
 :skolemid |1233|
 :pattern ( (_module.__default.SMN_k_k ($LS $ly@@43) |xs#0@@47| |n#0@@38| (Lit |len#0@@24|)))
))))
(assert  (=> (<= 52 $FunctionContextHeight) (forall (($ly@@44 T@U) (|xs#0@@48| T@U) (|n#0@@39| T@U) (|len#0@@25| T@U) ) (!  (=> (and (and (and (and (= (type $ly@@44) LayerTypeType) (= (type |xs#0@@48|) DatatypeTypeType)) (= (type |n#0@@39|) BoxType)) (= (type |len#0@@25|) BoxType)) (or (|_module.__default.SMN_k_k#canCall| (Lit |xs#0@@48|) (Lit |n#0@@39|) (Lit |len#0@@25|)) (and (not (= 52 $FunctionContextHeight)) (and (and (and ($Is |xs#0@@48| (Tclass._module.List |#$AbInt|)) ($IsBox |n#0@@39| |#$AbInt|)) ($IsBox |len#0@@25| |#$AbInt|)) (= (Lit |len#0@@25|) (Lit (_module.__default.Length ($LS $LZ) (Lit |xs#0@@48|)))))))) (and (and (|$IsA#_module.List| (Lit |xs#0@@48|)) (=> (not (|_module.List#Equal| |xs#0@@48| |#_module.List.Nil|)) (and (and (|_module.__default.AbDiv2#canCall| (Lit |len#0@@25|)) (|_module.__default.AbInc1#canCall| (_module.__default.AbDiv2 (Lit |len#0@@25|)))) (let ((|half#2@@1| (_module.__default.AbInc1 (_module.__default.AbDiv2 (Lit |len#0@@25|)))))
 (and (and (|_module.__default.AbInc#canCall| (Lit |n#0@@39|) |half#2@@1|) (|_module.__default.Split#canCall| (Lit |xs#0@@48|) (_module.__default.AbInc (Lit |n#0@@39|) |half#2@@1|))) (let ((|R#2@@4| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@48|) (_module.__default.AbInc (Lit |n#0@@39|) |half#2@@1|))))))
(let ((|L#2@@4| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@48|) (_module.__default.AbInc (Lit |n#0@@39|) |half#2@@1|))))))
 (and (|_module.__default.Length#canCall| |L#2@@4|) (let ((|llen#2@@3| (_module.__default.Length ($LS $LZ) |L#2@@4|)))
 (and (and (|_module.__default.AbLt#canCall| |llen#2@@3| |half#2@@1|) (=> (_module.__default.AbLt |llen#2@@3| |half#2@@1|) (|_module.__default.SMN_k_k#canCall| |L#2@@4| (Lit |n#0@@39|) |llen#2@@3|))) (=> (not (_module.__default.AbLt |llen#2@@3| |half#2@@1|)) (and (and (|_module.__default.AbInc#canCall| (Lit |n#0@@39|) |llen#2@@3|) (|_module.__default.AbDec#canCall| (Lit |len#0@@25|) |llen#2@@3|)) (|_module.__default.SMN_k_k#canCall| |R#2@@4| (_module.__default.AbInc (Lit |n#0@@39|) |llen#2@@3|) (_module.__default.AbDec (Lit |len#0@@25|) |llen#2@@3|)))))))))))))) (= (_module.__default.SMN_k_k ($LS $ly@@44) (Lit |xs#0@@48|) (Lit |n#0@@39|) (Lit |len#0@@25|)) (ite (|_module.List#Equal| |xs#0@@48| |#_module.List.Nil|) |n#0@@39| (let ((|half#2@@2| (_module.__default.AbInc1 (_module.__default.AbDiv2 (Lit |len#0@@25|)))))
(let ((|R#2@@5| ($Unbox DatatypeTypeType (_System.Tuple2._1 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@48|) (_module.__default.AbInc (Lit |n#0@@39|) |half#2@@2|))))))
(let ((|L#2@@5| ($Unbox DatatypeTypeType (_System.Tuple2._0 (_module.__default.Split ($LS $LZ) (Lit |xs#0@@48|) (_module.__default.AbInc (Lit |n#0@@39|) |half#2@@2|))))))
(let ((|llen#2@@4| (_module.__default.Length ($LS $LZ) |L#2@@5|)))
(ite (_module.__default.AbLt |llen#2@@4| |half#2@@2|) (_module.__default.SMN_k_k ($LS $ly@@44) |L#2@@5| (Lit |n#0@@39|) |llen#2@@4|) (_module.__default.SMN_k_k ($LS $ly@@44) |R#2@@5| (_module.__default.AbInc (Lit |n#0@@39|) |llen#2@@4|) (_module.__default.AbDec (Lit |len#0@@25|) |llen#2@@4|)))))))))))
 :qid |SMNADTLi.419:17|
 :weight 3
 :skolemid |1234|
 :pattern ( (_module.__default.SMN_k_k ($LS $ly@@44) (Lit |xs#0@@48|) (Lit |n#0@@39|) (Lit |len#0@@25|)))
))))
(assert  (and (and (and (and (and (and (and (forall ((arg0@@215 T@T) (arg1@@101 T@T) ) (! (= (Ctor (MapType5Type arg0@@215 arg1@@101)) 26)
 :qid |ctor:MapType5Type|
)) (forall ((arg0@@216 T@T) (arg1@@102 T@T) ) (! (= (MapType5TypeInv0 (MapType5Type arg0@@216 arg1@@102)) arg0@@216)
 :qid |typeInv:MapType5TypeInv0|
 :pattern ( (MapType5Type arg0@@216 arg1@@102))
))) (forall ((arg0@@217 T@T) (arg1@@103 T@T) ) (! (= (MapType5TypeInv1 (MapType5Type arg0@@217 arg1@@103)) arg1@@103)
 :qid |typeInv:MapType5TypeInv1|
 :pattern ( (MapType5Type arg0@@217 arg1@@103))
))) (forall ((arg0@@218 T@U) (arg1@@104 T@U) (arg2@@50 T@U) ) (! (let ((aVar1@@5 (MapType5TypeInv1 (type arg0@@218))))
(= (type (MapType5Select arg0@@218 arg1@@104 arg2@@50)) aVar1@@5))
 :qid |funType:MapType5Select|
 :pattern ( (MapType5Select arg0@@218 arg1@@104 arg2@@50))
))) (forall ((arg0@@219 T@U) (arg1@@105 T@U) (arg2@@51 T@U) (arg3@@28 T@U) ) (! (let ((aVar1@@6 (type arg3@@28)))
(let ((aVar0@@3 (type arg1@@105)))
(= (type (MapType5Store arg0@@219 arg1@@105 arg2@@51 arg3@@28)) (MapType5Type aVar0@@3 aVar1@@6))))
 :qid |funType:MapType5Store|
 :pattern ( (MapType5Store arg0@@219 arg1@@105 arg2@@51 arg3@@28))
))) (forall ((m@@42 T@U) (x0@@20 T@U) (x1@@14 T@U) (val@@21 T@U) ) (! (let ((aVar1@@7 (MapType5TypeInv1 (type m@@42))))
 (=> (= (type val@@21) aVar1@@7) (= (MapType5Select (MapType5Store m@@42 x0@@20 x1@@14 val@@21) x0@@20 x1@@14) val@@21)))
 :qid |mapAx0:MapType5Select|
 :weight 0
))) (and (and (forall ((val@@22 T@U) (m@@43 T@U) (x0@@21 T@U) (x1@@15 T@U) (y0@@15 T@U) (y1@@11 T@U) ) (!  (or (= x0@@21 y0@@15) (= (MapType5Select (MapType5Store m@@43 x0@@21 x1@@15 val@@22) y0@@15 y1@@11) (MapType5Select m@@43 y0@@15 y1@@11)))
 :qid |mapAx1:MapType5Select:0|
 :weight 0
)) (forall ((val@@23 T@U) (m@@44 T@U) (x0@@22 T@U) (x1@@16 T@U) (y0@@16 T@U) (y1@@12 T@U) ) (!  (or (= x1@@16 y1@@12) (= (MapType5Select (MapType5Store m@@44 x0@@22 x1@@16 val@@23) y0@@16 y1@@12) (MapType5Select m@@44 y0@@16 y1@@12)))
 :qid |mapAx1:MapType5Select:1|
 :weight 0
))) (forall ((val@@24 T@U) (m@@45 T@U) (x0@@23 T@U) (x1@@17 T@U) (y0@@17 T@U) (y1@@13 T@U) ) (!  (or true (= (MapType5Select (MapType5Store m@@45 x0@@23 x1@@17 val@@24) y0@@17 y1@@13) (MapType5Select m@@45 y0@@17 y1@@13)))
 :qid |mapAx2:MapType5Select|
 :weight 0
)))) (forall ((arg0@@220 T@U) (arg1@@106 T@U) (arg2@@52 T@U) (arg3@@29 Bool) ) (! (= (type (|lambda#0| arg0@@220 arg1@@106 arg2@@52 arg3@@29)) (MapType5Type refType boolType))
 :qid |funType:lambda#0|
 :pattern ( (|lambda#0| arg0@@220 arg1@@106 arg2@@52 arg3@@29))
))))
(assert (forall (($o@@9 T@U) ($f T@U) (|l#0| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ) (! (let ((alpha@@6 (FieldTypeInv0 (type $f))))
 (=> (and (and (and (and (= (type $o@@9) refType) (= (type $f) (FieldType alpha@@6))) (= (type |l#0|) refType)) (= (type |l#1|) (MapType0Type refType MapType1Type))) (= (type |l#2|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@9 $f))  (=> (and (not (= $o@@9 |l#0|)) (U_2_bool (MapType1Select (MapType0Select |l#1| $o@@9) |l#2|))) |l#3|))))
 :qid |SMNADTLi.14:11|
 :skolemid |1286|
 :pattern ( (MapType5Select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@9 $f))
)))
(assert (forall ((arg0@@221 T@U) (arg1@@107 T@U) (arg2@@53 T@U) (arg3@@30 Bool) ) (! (= (type (|lambda#1| arg0@@221 arg1@@107 arg2@@53 arg3@@30)) (MapType5Type refType boolType))
 :qid |funType:lambda#1|
 :pattern ( (|lambda#1| arg0@@221 arg1@@107 arg2@@53 arg3@@30))
)))
(assert (forall (($o@@10 T@U) ($f@@0 T@U) (|l#0@@0| T@U) (|l#1@@0| T@U) (|l#2@@0| T@U) (|l#3@@0| Bool) ) (! (let ((alpha@@7 (FieldTypeInv0 (type $f@@0))))
 (=> (and (and (and (and (= (type $o@@10) refType) (= (type $f@@0) (FieldType alpha@@7))) (= (type |l#0@@0|) refType)) (= (type |l#1@@0|) (MapType0Type refType MapType1Type))) (= (type |l#2@@0|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@10 $f@@0))  (=> (and (not (= $o@@10 |l#0@@0|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@0| $o@@10) |l#2@@0|))) |l#3@@0|))))
 :qid |SMNADTLi.14:11|
 :skolemid |1287|
 :pattern ( (MapType5Select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@10 $f@@0))
)))
(assert (forall ((arg0@@222 T@U) (arg1@@108 T@U) (arg2@@54 T@U) (arg3@@31 Bool) ) (! (= (type (|lambda#2| arg0@@222 arg1@@108 arg2@@54 arg3@@31)) (MapType5Type refType boolType))
 :qid |funType:lambda#2|
 :pattern ( (|lambda#2| arg0@@222 arg1@@108 arg2@@54 arg3@@31))
)))
(assert (forall (($o@@11 T@U) ($f@@1 T@U) (|l#0@@1| T@U) (|l#1@@1| T@U) (|l#2@@1| T@U) (|l#3@@1| Bool) ) (! (let ((alpha@@8 (FieldTypeInv0 (type $f@@1))))
 (=> (and (and (and (and (= (type $o@@11) refType) (= (type $f@@1) (FieldType alpha@@8))) (= (type |l#0@@1|) refType)) (= (type |l#1@@1|) (MapType0Type refType MapType1Type))) (= (type |l#2@@1|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#2| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@11 $f@@1))  (=> (and (not (= $o@@11 |l#0@@1|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@1| $o@@11) |l#2@@1|))) |l#3@@1|))))
 :qid |SMNADTLi.15:11|
 :skolemid |1288|
 :pattern ( (MapType5Select (|lambda#2| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@11 $f@@1))
)))
(assert (forall ((arg0@@223 T@U) (arg1@@109 T@U) (arg2@@55 T@U) (arg3@@32 Bool) ) (! (= (type (|lambda#3| arg0@@223 arg1@@109 arg2@@55 arg3@@32)) (MapType5Type refType boolType))
 :qid |funType:lambda#3|
 :pattern ( (|lambda#3| arg0@@223 arg1@@109 arg2@@55 arg3@@32))
)))
(assert (forall (($o@@12 T@U) ($f@@2 T@U) (|l#0@@2| T@U) (|l#1@@2| T@U) (|l#2@@2| T@U) (|l#3@@2| Bool) ) (! (let ((alpha@@9 (FieldTypeInv0 (type $f@@2))))
 (=> (and (and (and (and (= (type $o@@12) refType) (= (type $f@@2) (FieldType alpha@@9))) (= (type |l#0@@2|) refType)) (= (type |l#1@@2|) (MapType0Type refType MapType1Type))) (= (type |l#2@@2|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#3| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@12 $f@@2))  (=> (and (not (= $o@@12 |l#0@@2|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@2| $o@@12) |l#2@@2|))) |l#3@@2|))))
 :qid |SMNADTLi.15:11|
 :skolemid |1289|
 :pattern ( (MapType5Select (|lambda#3| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@12 $f@@2))
)))
(assert (forall ((arg0@@224 T@U) (arg1@@110 T@U) (arg2@@56 T@U) (arg3@@33 Bool) ) (! (= (type (|lambda#4| arg0@@224 arg1@@110 arg2@@56 arg3@@33)) (MapType5Type refType boolType))
 :qid |funType:lambda#4|
 :pattern ( (|lambda#4| arg0@@224 arg1@@110 arg2@@56 arg3@@33))
)))
(assert (forall (($o@@13 T@U) ($f@@3 T@U) (|l#0@@3| T@U) (|l#1@@3| T@U) (|l#2@@3| T@U) (|l#3@@3| Bool) ) (! (let ((alpha@@10 (FieldTypeInv0 (type $f@@3))))
 (=> (and (and (and (and (= (type $o@@13) refType) (= (type $f@@3) (FieldType alpha@@10))) (= (type |l#0@@3|) refType)) (= (type |l#1@@3|) (MapType0Type refType MapType1Type))) (= (type |l#2@@3|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#4| |l#0@@3| |l#1@@3| |l#2@@3| |l#3@@3|) $o@@13 $f@@3))  (=> (and (not (= $o@@13 |l#0@@3|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@3| $o@@13) |l#2@@3|))) |l#3@@3|))))
 :qid |SMNADTLi.22:17|
 :skolemid |1290|
 :pattern ( (MapType5Select (|lambda#4| |l#0@@3| |l#1@@3| |l#2@@3| |l#3@@3|) $o@@13 $f@@3))
)))
(assert (forall ((arg0@@225 T@U) (arg1@@111 T@U) (arg2@@57 T@U) (arg3@@34 Bool) ) (! (= (type (|lambda#5| arg0@@225 arg1@@111 arg2@@57 arg3@@34)) (MapType5Type refType boolType))
 :qid |funType:lambda#5|
 :pattern ( (|lambda#5| arg0@@225 arg1@@111 arg2@@57 arg3@@34))
)))
(assert (forall (($o@@14 T@U) ($f@@4 T@U) (|l#0@@4| T@U) (|l#1@@4| T@U) (|l#2@@4| T@U) (|l#3@@4| Bool) ) (! (let ((alpha@@11 (FieldTypeInv0 (type $f@@4))))
 (=> (and (and (and (and (= (type $o@@14) refType) (= (type $f@@4) (FieldType alpha@@11))) (= (type |l#0@@4|) refType)) (= (type |l#1@@4|) (MapType0Type refType MapType1Type))) (= (type |l#2@@4|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#5| |l#0@@4| |l#1@@4| |l#2@@4| |l#3@@4|) $o@@14 $f@@4))  (=> (and (not (= $o@@14 |l#0@@4|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@4| $o@@14) |l#2@@4|))) |l#3@@4|))))
 :qid |SMNADTLi.32:17|
 :skolemid |1291|
 :pattern ( (MapType5Select (|lambda#5| |l#0@@4| |l#1@@4| |l#2@@4| |l#3@@4|) $o@@14 $f@@4))
)))
(assert (forall ((arg0@@226 T@U) (arg1@@112 T@U) (arg2@@58 T@U) (arg3@@35 Bool) ) (! (= (type (|lambda#6| arg0@@226 arg1@@112 arg2@@58 arg3@@35)) (MapType5Type refType boolType))
 :qid |funType:lambda#6|
 :pattern ( (|lambda#6| arg0@@226 arg1@@112 arg2@@58 arg3@@35))
)))
(assert (forall (($o@@15 T@U) ($f@@5 T@U) (|l#0@@5| T@U) (|l#1@@5| T@U) (|l#2@@5| T@U) (|l#3@@5| Bool) ) (! (let ((alpha@@12 (FieldTypeInv0 (type $f@@5))))
 (=> (and (and (and (and (= (type $o@@15) refType) (= (type $f@@5) (FieldType alpha@@12))) (= (type |l#0@@5|) refType)) (= (type |l#1@@5|) (MapType0Type refType MapType1Type))) (= (type |l#2@@5|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#6| |l#0@@5| |l#1@@5| |l#2@@5| |l#3@@5|) $o@@15 $f@@5))  (=> (and (not (= $o@@15 |l#0@@5|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@5| $o@@15) |l#2@@5|))) |l#3@@5|))))
 :qid |SMNADTLi.102:17|
 :skolemid |1292|
 :pattern ( (MapType5Select (|lambda#6| |l#0@@5| |l#1@@5| |l#2@@5| |l#3@@5|) $o@@15 $f@@5))
)))
(assert (forall ((arg0@@227 T@U) (arg1@@113 T@U) (arg2@@59 T@U) (arg3@@36 Bool) ) (! (= (type (|lambda#7| arg0@@227 arg1@@113 arg2@@59 arg3@@36)) (MapType5Type refType boolType))
 :qid |funType:lambda#7|
 :pattern ( (|lambda#7| arg0@@227 arg1@@113 arg2@@59 arg3@@36))
)))
(assert (forall (($o@@16 T@U) ($f@@6 T@U) (|l#0@@6| T@U) (|l#1@@6| T@U) (|l#2@@6| T@U) (|l#3@@6| Bool) ) (! (let ((alpha@@13 (FieldTypeInv0 (type $f@@6))))
 (=> (and (and (and (and (= (type $o@@16) refType) (= (type $f@@6) (FieldType alpha@@13))) (= (type |l#0@@6|) refType)) (= (type |l#1@@6|) (MapType0Type refType MapType1Type))) (= (type |l#2@@6|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#7| |l#0@@6| |l#1@@6| |l#2@@6| |l#3@@6|) $o@@16 $f@@6))  (=> (and (not (= $o@@16 |l#0@@6|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@6| $o@@16) |l#2@@6|))) |l#3@@6|))))
 :qid |SMNADTLi.102:17|
 :skolemid |1293|
 :pattern ( (MapType5Select (|lambda#7| |l#0@@6| |l#1@@6| |l#2@@6| |l#3@@6|) $o@@16 $f@@6))
)))
(assert (forall ((arg0@@228 T@U) (arg1@@114 T@U) (arg2@@60 T@U) (arg3@@37 Bool) ) (! (= (type (|lambda#8| arg0@@228 arg1@@114 arg2@@60 arg3@@37)) (MapType5Type refType boolType))
 :qid |funType:lambda#8|
 :pattern ( (|lambda#8| arg0@@228 arg1@@114 arg2@@60 arg3@@37))
)))
(assert (forall (($o@@17 T@U) ($f@@7 T@U) (|l#0@@7| T@U) (|l#1@@7| T@U) (|l#2@@7| T@U) (|l#3@@7| Bool) ) (! (let ((alpha@@14 (FieldTypeInv0 (type $f@@7))))
 (=> (and (and (and (and (= (type $o@@17) refType) (= (type $f@@7) (FieldType alpha@@14))) (= (type |l#0@@7|) refType)) (= (type |l#1@@7|) (MapType0Type refType MapType1Type))) (= (type |l#2@@7|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#8| |l#0@@7| |l#1@@7| |l#2@@7| |l#3@@7|) $o@@17 $f@@7))  (=> (and (not (= $o@@17 |l#0@@7|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@7| $o@@17) |l#2@@7|))) |l#3@@7|))))
 :qid |SMNADTLi.109:17|
 :skolemid |1294|
 :pattern ( (MapType5Select (|lambda#8| |l#0@@7| |l#1@@7| |l#2@@7| |l#3@@7|) $o@@17 $f@@7))
)))
(assert (forall ((arg0@@229 T@U) (arg1@@115 T@U) (arg2@@61 T@U) (arg3@@38 Bool) ) (! (= (type (|lambda#9| arg0@@229 arg1@@115 arg2@@61 arg3@@38)) (MapType5Type refType boolType))
 :qid |funType:lambda#9|
 :pattern ( (|lambda#9| arg0@@229 arg1@@115 arg2@@61 arg3@@38))
)))
(assert (forall (($o@@18 T@U) ($f@@8 T@U) (|l#0@@8| T@U) (|l#1@@8| T@U) (|l#2@@8| T@U) (|l#3@@8| Bool) ) (! (let ((alpha@@15 (FieldTypeInv0 (type $f@@8))))
 (=> (and (and (and (and (= (type $o@@18) refType) (= (type $f@@8) (FieldType alpha@@15))) (= (type |l#0@@8|) refType)) (= (type |l#1@@8|) (MapType0Type refType MapType1Type))) (= (type |l#2@@8|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#9| |l#0@@8| |l#1@@8| |l#2@@8| |l#3@@8|) $o@@18 $f@@8))  (=> (and (not (= $o@@18 |l#0@@8|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@8| $o@@18) |l#2@@8|))) |l#3@@8|))))
 :qid |SMNADTLi.109:17|
 :skolemid |1295|
 :pattern ( (MapType5Select (|lambda#9| |l#0@@8| |l#1@@8| |l#2@@8| |l#3@@8|) $o@@18 $f@@8))
)))
(assert (forall ((arg0@@230 T@U) (arg1@@116 T@U) (arg2@@62 T@U) ) (! (= (type (|lambda#10| arg0@@230 arg1@@116 arg2@@62)) (MapType0Type BoxType boolType))
 :qid |funType:lambda#10|
 :pattern ( (|lambda#10| arg0@@230 arg1@@116 arg2@@62))
)))
(assert (forall ((|$y#8| T@U) (|l#0@@9| T@U) (|l#1@@9| T@U) (|l#2@@9| T@U) ) (!  (=> (and (and (and (= (type |$y#8|) BoxType) (= (type |l#0@@9|) TyType)) (= (type |l#1@@9|) (MapType0Type BoxType boolType))) (= (type |l#2@@9|) BoxType)) (= (U_2_bool (MapType0Select (|lambda#10| |l#0@@9| |l#1@@9| |l#2@@9|) |$y#8|))  (and ($IsBox |$y#8| |l#0@@9|) (and (U_2_bool (MapType0Select |l#1@@9| |$y#8|)) (_module.__default.AbLt |$y#8| |l#2@@9|)))))
 :qid |SMNADTLi.128:23|
 :skolemid |1296|
 :pattern ( (MapType0Select (|lambda#10| |l#0@@9| |l#1@@9| |l#2@@9|) |$y#8|))
)))
(assert (forall ((arg0@@231 T@U) (arg1@@117 T@U) (arg2@@63 T@U) ) (! (= (type (|lambda#11| arg0@@231 arg1@@117 arg2@@63)) (MapType0Type BoxType boolType))
 :qid |funType:lambda#11|
 :pattern ( (|lambda#11| arg0@@231 arg1@@117 arg2@@63))
)))
(assert (forall ((|$y#7| T@U) (|l#0@@10| T@U) (|l#1@@10| T@U) (|l#2@@10| T@U) ) (!  (=> (and (and (and (= (type |$y#7|) BoxType) (= (type |l#0@@10|) TyType)) (= (type |l#1@@10|) (MapType0Type BoxType boolType))) (= (type |l#2@@10|) BoxType)) (= (U_2_bool (MapType0Select (|lambda#11| |l#0@@10| |l#1@@10| |l#2@@10|) |$y#7|))  (and ($IsBox |$y#7| |l#0@@10|) (and (U_2_bool (MapType0Select |l#1@@10| |$y#7|)) (not (_module.__default.AbLt |$y#7| |l#2@@10|))))))
 :qid |SMNADTLi.129:23|
 :skolemid |1297|
 :pattern ( (MapType0Select (|lambda#11| |l#0@@10| |l#1@@10| |l#2@@10|) |$y#7|))
)))
(assert (forall ((arg0@@232 T@U) (arg1@@118 T@U) (arg2@@64 T@U) (arg3@@39 Bool) ) (! (= (type (|lambda#18| arg0@@232 arg1@@118 arg2@@64 arg3@@39)) (MapType5Type refType boolType))
 :qid |funType:lambda#18|
 :pattern ( (|lambda#18| arg0@@232 arg1@@118 arg2@@64 arg3@@39))
)))
(assert (forall (($o@@19 T@U) ($f@@9 T@U) (|l#0@@11| T@U) (|l#1@@11| T@U) (|l#2@@11| T@U) (|l#3@@9| Bool) ) (! (let ((alpha@@16 (FieldTypeInv0 (type $f@@9))))
 (=> (and (and (and (and (= (type $o@@19) refType) (= (type $f@@9) (FieldType alpha@@16))) (= (type |l#0@@11|) refType)) (= (type |l#1@@11|) (MapType0Type refType MapType1Type))) (= (type |l#2@@11|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#18| |l#0@@11| |l#1@@11| |l#2@@11| |l#3@@9|) $o@@19 $f@@9))  (=> (and (not (= $o@@19 |l#0@@11|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@11| $o@@19) |l#2@@11|))) |l#3@@9|))))
 :qid |SMNADTLi.125:7|
 :skolemid |1298|
 :pattern ( (MapType5Select (|lambda#18| |l#0@@11| |l#1@@11| |l#2@@11| |l#3@@9|) $o@@19 $f@@9))
)))
(assert (forall ((arg0@@233 T@U) (arg1@@119 T@U) (arg2@@65 T@U) (arg3@@40 Bool) ) (! (= (type (|lambda#21| arg0@@233 arg1@@119 arg2@@65 arg3@@40)) (MapType5Type refType boolType))
 :qid |funType:lambda#21|
 :pattern ( (|lambda#21| arg0@@233 arg1@@119 arg2@@65 arg3@@40))
)))
(assert (forall (($o@@20 T@U) ($f@@10 T@U) (|l#0@@12| T@U) (|l#1@@12| T@U) (|l#2@@12| T@U) (|l#3@@10| Bool) ) (! (let ((alpha@@17 (FieldTypeInv0 (type $f@@10))))
 (=> (and (and (and (and (= (type $o@@20) refType) (= (type $f@@10) (FieldType alpha@@17))) (= (type |l#0@@12|) refType)) (= (type |l#1@@12|) (MapType0Type refType MapType1Type))) (= (type |l#2@@12|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#21| |l#0@@12| |l#1@@12| |l#2@@12| |l#3@@10|) $o@@20 $f@@10))  (=> (and (not (= $o@@20 |l#0@@12|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@12| $o@@20) |l#2@@12|))) |l#3@@10|))))
 :qid |SMNADTLi.138:10|
 :skolemid |1299|
 :pattern ( (MapType5Select (|lambda#21| |l#0@@12| |l#1@@12| |l#2@@12| |l#3@@10|) $o@@20 $f@@10))
)))
(assert (forall ((arg0@@234 T@U) (arg1@@120 T@U) (arg2@@66 T@U) (arg3@@41 Bool) ) (! (= (type (|lambda#22| arg0@@234 arg1@@120 arg2@@66 arg3@@41)) (MapType5Type refType boolType))
 :qid |funType:lambda#22|
 :pattern ( (|lambda#22| arg0@@234 arg1@@120 arg2@@66 arg3@@41))
)))
(assert (forall (($o@@21 T@U) ($f@@11 T@U) (|l#0@@13| T@U) (|l#1@@13| T@U) (|l#2@@13| T@U) (|l#3@@11| Bool) ) (! (let ((alpha@@18 (FieldTypeInv0 (type $f@@11))))
 (=> (and (and (and (and (= (type $o@@21) refType) (= (type $f@@11) (FieldType alpha@@18))) (= (type |l#0@@13|) refType)) (= (type |l#1@@13|) (MapType0Type refType MapType1Type))) (= (type |l#2@@13|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#22| |l#0@@13| |l#1@@13| |l#2@@13| |l#3@@11|) $o@@21 $f@@11))  (=> (and (not (= $o@@21 |l#0@@13|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@13| $o@@21) |l#2@@13|))) |l#3@@11|))))
 :qid |SMNADTLi.138:10|
 :skolemid |1300|
 :pattern ( (MapType5Select (|lambda#22| |l#0@@13| |l#1@@13| |l#2@@13| |l#3@@11|) $o@@21 $f@@11))
)))
(assert (forall ((arg0@@235 T@U) (arg1@@121 T@U) (arg2@@67 T@U) (arg3@@42 Bool) ) (! (= (type (|lambda#23| arg0@@235 arg1@@121 arg2@@67 arg3@@42)) (MapType5Type refType boolType))
 :qid |funType:lambda#23|
 :pattern ( (|lambda#23| arg0@@235 arg1@@121 arg2@@67 arg3@@42))
)))
(assert (forall (($o@@22 T@U) ($f@@12 T@U) (|l#0@@14| T@U) (|l#1@@14| T@U) (|l#2@@14| T@U) (|l#3@@12| Bool) ) (! (let ((alpha@@19 (FieldTypeInv0 (type $f@@12))))
 (=> (and (and (and (and (= (type $o@@22) refType) (= (type $f@@12) (FieldType alpha@@19))) (= (type |l#0@@14|) refType)) (= (type |l#1@@14|) (MapType0Type refType MapType1Type))) (= (type |l#2@@14|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#23| |l#0@@14| |l#1@@14| |l#2@@14| |l#3@@12|) $o@@22 $f@@12))  (=> (and (not (= $o@@22 |l#0@@14|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@14| $o@@22) |l#2@@14|))) |l#3@@12|))))
 :qid |SMNADTLi.145:7|
 :skolemid |1301|
 :pattern ( (MapType5Select (|lambda#23| |l#0@@14| |l#1@@14| |l#2@@14| |l#3@@12|) $o@@22 $f@@12))
)))
(assert (forall ((arg0@@236 T@U) (arg1@@122 T@U) (arg2@@68 T@U) (arg3@@43 Bool) ) (! (= (type (|lambda#24| arg0@@236 arg1@@122 arg2@@68 arg3@@43)) (MapType5Type refType boolType))
 :qid |funType:lambda#24|
 :pattern ( (|lambda#24| arg0@@236 arg1@@122 arg2@@68 arg3@@43))
)))
(assert (forall (($o@@23 T@U) ($f@@13 T@U) (|l#0@@15| T@U) (|l#1@@15| T@U) (|l#2@@15| T@U) (|l#3@@13| Bool) ) (! (let ((alpha@@20 (FieldTypeInv0 (type $f@@13))))
 (=> (and (and (and (and (= (type $o@@23) refType) (= (type $f@@13) (FieldType alpha@@20))) (= (type |l#0@@15|) refType)) (= (type |l#1@@15|) (MapType0Type refType MapType1Type))) (= (type |l#2@@15|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#24| |l#0@@15| |l#1@@15| |l#2@@15| |l#3@@13|) $o@@23 $f@@13))  (=> (and (not (= $o@@23 |l#0@@15|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@15| $o@@23) |l#2@@15|))) |l#3@@13|))))
 :qid |SMNADTLi.154:11|
 :skolemid |1302|
 :pattern ( (MapType5Select (|lambda#24| |l#0@@15| |l#1@@15| |l#2@@15| |l#3@@13|) $o@@23 $f@@13))
)))
(assert (forall ((arg0@@237 T@U) (arg1@@123 T@U) (arg2@@69 T@U) (arg3@@44 Bool) ) (! (= (type (|lambda#25| arg0@@237 arg1@@123 arg2@@69 arg3@@44)) (MapType5Type refType boolType))
 :qid |funType:lambda#25|
 :pattern ( (|lambda#25| arg0@@237 arg1@@123 arg2@@69 arg3@@44))
)))
(assert (forall (($o@@24 T@U) ($f@@14 T@U) (|l#0@@16| T@U) (|l#1@@16| T@U) (|l#2@@16| T@U) (|l#3@@14| Bool) ) (! (let ((alpha@@21 (FieldTypeInv0 (type $f@@14))))
 (=> (and (and (and (and (= (type $o@@24) refType) (= (type $f@@14) (FieldType alpha@@21))) (= (type |l#0@@16|) refType)) (= (type |l#1@@16|) (MapType0Type refType MapType1Type))) (= (type |l#2@@16|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#25| |l#0@@16| |l#1@@16| |l#2@@16| |l#3@@14|) $o@@24 $f@@14))  (=> (and (not (= $o@@24 |l#0@@16|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@16| $o@@24) |l#2@@16|))) |l#3@@14|))))
 :qid |SMNADTLi.154:11|
 :skolemid |1303|
 :pattern ( (MapType5Select (|lambda#25| |l#0@@16| |l#1@@16| |l#2@@16| |l#3@@14|) $o@@24 $f@@14))
)))
(assert (forall ((arg0@@238 T@U) (arg1@@124 T@U) (arg2@@70 T@U) (arg3@@45 Bool) ) (! (= (type (|lambda#26| arg0@@238 arg1@@124 arg2@@70 arg3@@45)) (MapType5Type refType boolType))
 :qid |funType:lambda#26|
 :pattern ( (|lambda#26| arg0@@238 arg1@@124 arg2@@70 arg3@@45))
)))
(assert (forall (($o@@25 T@U) ($f@@15 T@U) (|l#0@@17| T@U) (|l#1@@17| T@U) (|l#2@@17| T@U) (|l#3@@15| Bool) ) (! (let ((alpha@@22 (FieldTypeInv0 (type $f@@15))))
 (=> (and (and (and (and (= (type $o@@25) refType) (= (type $f@@15) (FieldType alpha@@22))) (= (type |l#0@@17|) refType)) (= (type |l#1@@17|) (MapType0Type refType MapType1Type))) (= (type |l#2@@17|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#26| |l#0@@17| |l#1@@17| |l#2@@17| |l#3@@15|) $o@@25 $f@@15))  (=> (and (not (= $o@@25 |l#0@@17|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@17| $o@@25) |l#2@@17|))) |l#3@@15|))))
 :qid |SMNADTLi.164:7|
 :skolemid |1304|
 :pattern ( (MapType5Select (|lambda#26| |l#0@@17| |l#1@@17| |l#2@@17| |l#3@@15|) $o@@25 $f@@15))
)))
(assert (forall ((arg0@@239 T@U) (arg1@@125 T@U) (arg2@@71 T@U) (arg3@@46 Bool) ) (! (= (type (|lambda#27| arg0@@239 arg1@@125 arg2@@71 arg3@@46)) (MapType5Type refType boolType))
 :qid |funType:lambda#27|
 :pattern ( (|lambda#27| arg0@@239 arg1@@125 arg2@@71 arg3@@46))
)))
(assert (forall (($o@@26 T@U) ($f@@16 T@U) (|l#0@@18| T@U) (|l#1@@18| T@U) (|l#2@@18| T@U) (|l#3@@16| Bool) ) (! (let ((alpha@@23 (FieldTypeInv0 (type $f@@16))))
 (=> (and (and (and (and (= (type $o@@26) refType) (= (type $f@@16) (FieldType alpha@@23))) (= (type |l#0@@18|) refType)) (= (type |l#1@@18|) (MapType0Type refType MapType1Type))) (= (type |l#2@@18|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#27| |l#0@@18| |l#1@@18| |l#2@@18| |l#3@@16|) $o@@26 $f@@16))  (=> (and (not (= $o@@26 |l#0@@18|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@18| $o@@26) |l#2@@18|))) |l#3@@16|))))
 :qid |SMNADTLi.179:7|
 :skolemid |1305|
 :pattern ( (MapType5Select (|lambda#27| |l#0@@18| |l#1@@18| |l#2@@18| |l#3@@16|) $o@@26 $f@@16))
)))
(assert (forall ((arg0@@240 T@U) (arg1@@126 T@U) (arg2@@72 T@U) (arg3@@47 Bool) ) (! (= (type (|lambda#28| arg0@@240 arg1@@126 arg2@@72 arg3@@47)) (MapType5Type refType boolType))
 :qid |funType:lambda#28|
 :pattern ( (|lambda#28| arg0@@240 arg1@@126 arg2@@72 arg3@@47))
)))
(assert (forall (($o@@27 T@U) ($f@@17 T@U) (|l#0@@19| T@U) (|l#1@@19| T@U) (|l#2@@19| T@U) (|l#3@@17| Bool) ) (! (let ((alpha@@24 (FieldTypeInv0 (type $f@@17))))
 (=> (and (and (and (and (= (type $o@@27) refType) (= (type $f@@17) (FieldType alpha@@24))) (= (type |l#0@@19|) refType)) (= (type |l#1@@19|) (MapType0Type refType MapType1Type))) (= (type |l#2@@19|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#28| |l#0@@19| |l#1@@19| |l#2@@19| |l#3@@17|) $o@@27 $f@@17))  (=> (and (not (= $o@@27 |l#0@@19|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@19| $o@@27) |l#2@@19|))) |l#3@@17|))))
 :qid |SMNADTLi.193:10|
 :skolemid |1306|
 :pattern ( (MapType5Select (|lambda#28| |l#0@@19| |l#1@@19| |l#2@@19| |l#3@@17|) $o@@27 $f@@17))
)))
(assert (forall ((arg0@@241 T@U) (arg1@@127 T@U) (arg2@@73 T@U) (arg3@@48 Bool) ) (! (= (type (|lambda#29| arg0@@241 arg1@@127 arg2@@73 arg3@@48)) (MapType5Type refType boolType))
 :qid |funType:lambda#29|
 :pattern ( (|lambda#29| arg0@@241 arg1@@127 arg2@@73 arg3@@48))
)))
(assert (forall (($o@@28 T@U) ($f@@18 T@U) (|l#0@@20| T@U) (|l#1@@20| T@U) (|l#2@@20| T@U) (|l#3@@18| Bool) ) (! (let ((alpha@@25 (FieldTypeInv0 (type $f@@18))))
 (=> (and (and (and (and (= (type $o@@28) refType) (= (type $f@@18) (FieldType alpha@@25))) (= (type |l#0@@20|) refType)) (= (type |l#1@@20|) (MapType0Type refType MapType1Type))) (= (type |l#2@@20|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#29| |l#0@@20| |l#1@@20| |l#2@@20| |l#3@@18|) $o@@28 $f@@18))  (=> (and (not (= $o@@28 |l#0@@20|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@20| $o@@28) |l#2@@20|))) |l#3@@18|))))
 :qid |SMNADTLi.193:10|
 :skolemid |1307|
 :pattern ( (MapType5Select (|lambda#29| |l#0@@20| |l#1@@20| |l#2@@20| |l#3@@18|) $o@@28 $f@@18))
)))
(assert (forall ((arg0@@242 T@U) (arg1@@128 T@U) (arg2@@74 T@U) (arg3@@49 Bool) ) (! (= (type (|lambda#30| arg0@@242 arg1@@128 arg2@@74 arg3@@49)) (MapType5Type refType boolType))
 :qid |funType:lambda#30|
 :pattern ( (|lambda#30| arg0@@242 arg1@@128 arg2@@74 arg3@@49))
)))
(assert (forall (($o@@29 T@U) ($f@@19 T@U) (|l#0@@21| T@U) (|l#1@@21| T@U) (|l#2@@21| T@U) (|l#3@@19| Bool) ) (! (let ((alpha@@26 (FieldTypeInv0 (type $f@@19))))
 (=> (and (and (and (and (= (type $o@@29) refType) (= (type $f@@19) (FieldType alpha@@26))) (= (type |l#0@@21|) refType)) (= (type |l#1@@21|) (MapType0Type refType MapType1Type))) (= (type |l#2@@21|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#30| |l#0@@21| |l#1@@21| |l#2@@21| |l#3@@19|) $o@@29 $f@@19))  (=> (and (not (= $o@@29 |l#0@@21|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@21| $o@@29) |l#2@@21|))) |l#3@@19|))))
 :qid |SMNADTLi.203:17|
 :skolemid |1308|
 :pattern ( (MapType5Select (|lambda#30| |l#0@@21| |l#1@@21| |l#2@@21| |l#3@@19|) $o@@29 $f@@19))
)))
(assert (forall ((arg0@@243 T@U) (arg1@@129 T@U) (arg2@@75 T@U) (arg3@@50 Bool) ) (! (= (type (|lambda#31| arg0@@243 arg1@@129 arg2@@75 arg3@@50)) (MapType5Type refType boolType))
 :qid |funType:lambda#31|
 :pattern ( (|lambda#31| arg0@@243 arg1@@129 arg2@@75 arg3@@50))
)))
(assert (forall (($o@@30 T@U) ($f@@20 T@U) (|l#0@@22| T@U) (|l#1@@22| T@U) (|l#2@@22| T@U) (|l#3@@20| Bool) ) (! (let ((alpha@@27 (FieldTypeInv0 (type $f@@20))))
 (=> (and (and (and (and (= (type $o@@30) refType) (= (type $f@@20) (FieldType alpha@@27))) (= (type |l#0@@22|) refType)) (= (type |l#1@@22|) (MapType0Type refType MapType1Type))) (= (type |l#2@@22|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#31| |l#0@@22| |l#1@@22| |l#2@@22| |l#3@@20|) $o@@30 $f@@20))  (=> (and (not (= $o@@30 |l#0@@22|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@22| $o@@30) |l#2@@22|))) |l#3@@20|))))
 :qid |SMNADTLi.203:17|
 :skolemid |1309|
 :pattern ( (MapType5Select (|lambda#31| |l#0@@22| |l#1@@22| |l#2@@22| |l#3@@20|) $o@@30 $f@@20))
)))
(assert (forall ((arg0@@244 T@U) (arg1@@130 T@U) (arg2@@76 T@U) (arg3@@51 Bool) ) (! (= (type (|lambda#32| arg0@@244 arg1@@130 arg2@@76 arg3@@51)) (MapType5Type refType boolType))
 :qid |funType:lambda#32|
 :pattern ( (|lambda#32| arg0@@244 arg1@@130 arg2@@76 arg3@@51))
)))
(assert (forall (($o@@31 T@U) ($f@@21 T@U) (|l#0@@23| T@U) (|l#1@@23| T@U) (|l#2@@23| T@U) (|l#3@@21| Bool) ) (! (let ((alpha@@28 (FieldTypeInv0 (type $f@@21))))
 (=> (and (and (and (and (= (type $o@@31) refType) (= (type $f@@21) (FieldType alpha@@28))) (= (type |l#0@@23|) refType)) (= (type |l#1@@23|) (MapType0Type refType MapType1Type))) (= (type |l#2@@23|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#32| |l#0@@23| |l#1@@23| |l#2@@23| |l#3@@21|) $o@@31 $f@@21))  (=> (and (not (= $o@@31 |l#0@@23|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@23| $o@@31) |l#2@@23|))) |l#3@@21|))))
 :qid |SMNADTLi.208:17|
 :skolemid |1310|
 :pattern ( (MapType5Select (|lambda#32| |l#0@@23| |l#1@@23| |l#2@@23| |l#3@@21|) $o@@31 $f@@21))
)))
(assert (forall ((arg0@@245 T@U) (arg1@@131 T@U) (arg2@@77 T@U) (arg3@@52 Bool) ) (! (= (type (|lambda#33| arg0@@245 arg1@@131 arg2@@77 arg3@@52)) (MapType5Type refType boolType))
 :qid |funType:lambda#33|
 :pattern ( (|lambda#33| arg0@@245 arg1@@131 arg2@@77 arg3@@52))
)))
(assert (forall (($o@@32 T@U) ($f@@22 T@U) (|l#0@@24| T@U) (|l#1@@24| T@U) (|l#2@@24| T@U) (|l#3@@22| Bool) ) (! (let ((alpha@@29 (FieldTypeInv0 (type $f@@22))))
 (=> (and (and (and (and (= (type $o@@32) refType) (= (type $f@@22) (FieldType alpha@@29))) (= (type |l#0@@24|) refType)) (= (type |l#1@@24|) (MapType0Type refType MapType1Type))) (= (type |l#2@@24|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#33| |l#0@@24| |l#1@@24| |l#2@@24| |l#3@@22|) $o@@32 $f@@22))  (=> (and (not (= $o@@32 |l#0@@24|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@24| $o@@32) |l#2@@24|))) |l#3@@22|))))
 :qid |SMNADTLi.208:17|
 :skolemid |1311|
 :pattern ( (MapType5Select (|lambda#33| |l#0@@24| |l#1@@24| |l#2@@24| |l#3@@22|) $o@@32 $f@@22))
)))
(assert (forall ((arg0@@246 T@U) (arg1@@132 T@U) (arg2@@78 T@U) (arg3@@53 Bool) ) (! (= (type (|lambda#34| arg0@@246 arg1@@132 arg2@@78 arg3@@53)) (MapType5Type refType boolType))
 :qid |funType:lambda#34|
 :pattern ( (|lambda#34| arg0@@246 arg1@@132 arg2@@78 arg3@@53))
)))
(assert (forall (($o@@33 T@U) ($f@@23 T@U) (|l#0@@25| T@U) (|l#1@@25| T@U) (|l#2@@25| T@U) (|l#3@@23| Bool) ) (! (let ((alpha@@30 (FieldTypeInv0 (type $f@@23))))
 (=> (and (and (and (and (= (type $o@@33) refType) (= (type $f@@23) (FieldType alpha@@30))) (= (type |l#0@@25|) refType)) (= (type |l#1@@25|) (MapType0Type refType MapType1Type))) (= (type |l#2@@25|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#34| |l#0@@25| |l#1@@25| |l#2@@25| |l#3@@23|) $o@@33 $f@@23))  (=> (and (not (= $o@@33 |l#0@@25|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@25| $o@@33) |l#2@@25|))) |l#3@@23|))))
 :qid |SMNADTLi.243:7|
 :skolemid |1312|
 :pattern ( (MapType5Select (|lambda#34| |l#0@@25| |l#1@@25| |l#2@@25| |l#3@@23|) $o@@33 $f@@23))
)))
(assert (forall ((arg0@@247 T@U) (arg1@@133 T@U) (arg2@@79 T@U) (arg3@@54 Bool) ) (! (= (type (|lambda#35| arg0@@247 arg1@@133 arg2@@79 arg3@@54)) (MapType5Type refType boolType))
 :qid |funType:lambda#35|
 :pattern ( (|lambda#35| arg0@@247 arg1@@133 arg2@@79 arg3@@54))
)))
(assert (forall (($o@@34 T@U) ($f@@24 T@U) (|l#0@@26| T@U) (|l#1@@26| T@U) (|l#2@@26| T@U) (|l#3@@24| Bool) ) (! (let ((alpha@@31 (FieldTypeInv0 (type $f@@24))))
 (=> (and (and (and (and (= (type $o@@34) refType) (= (type $f@@24) (FieldType alpha@@31))) (= (type |l#0@@26|) refType)) (= (type |l#1@@26|) (MapType0Type refType MapType1Type))) (= (type |l#2@@26|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#35| |l#0@@26| |l#1@@26| |l#2@@26| |l#3@@24|) $o@@34 $f@@24))  (=> (and (not (= $o@@34 |l#0@@26|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@26| $o@@34) |l#2@@26|))) |l#3@@24|))))
 :qid |SMNADTLi.254:7|
 :skolemid |1313|
 :pattern ( (MapType5Select (|lambda#35| |l#0@@26| |l#1@@26| |l#2@@26| |l#3@@24|) $o@@34 $f@@24))
)))
(assert (forall ((arg0@@248 T@U) (arg1@@134 T@U) (arg2@@80 T@U) (arg3@@55 Bool) ) (! (= (type (|lambda#36| arg0@@248 arg1@@134 arg2@@80 arg3@@55)) (MapType5Type refType boolType))
 :qid |funType:lambda#36|
 :pattern ( (|lambda#36| arg0@@248 arg1@@134 arg2@@80 arg3@@55))
)))
(assert (forall (($o@@35 T@U) ($f@@25 T@U) (|l#0@@27| T@U) (|l#1@@27| T@U) (|l#2@@27| T@U) (|l#3@@25| Bool) ) (! (let ((alpha@@32 (FieldTypeInv0 (type $f@@25))))
 (=> (and (and (and (and (= (type $o@@35) refType) (= (type $f@@25) (FieldType alpha@@32))) (= (type |l#0@@27|) refType)) (= (type |l#1@@27|) (MapType0Type refType MapType1Type))) (= (type |l#2@@27|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#36| |l#0@@27| |l#1@@27| |l#2@@27| |l#3@@25|) $o@@35 $f@@25))  (=> (and (not (= $o@@35 |l#0@@27|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@27| $o@@35) |l#2@@27|))) |l#3@@25|))))
 :qid |SMNADTLi.254:7|
 :skolemid |1314|
 :pattern ( (MapType5Select (|lambda#36| |l#0@@27| |l#1@@27| |l#2@@27| |l#3@@25|) $o@@35 $f@@25))
)))
(assert (forall ((arg0@@249 T@U) (arg1@@135 T@U) (arg2@@81 T@U) (arg3@@56 Bool) ) (! (= (type (|lambda#37| arg0@@249 arg1@@135 arg2@@81 arg3@@56)) (MapType5Type refType boolType))
 :qid |funType:lambda#37|
 :pattern ( (|lambda#37| arg0@@249 arg1@@135 arg2@@81 arg3@@56))
)))
(assert (forall (($o@@36 T@U) ($f@@26 T@U) (|l#0@@28| T@U) (|l#1@@28| T@U) (|l#2@@28| T@U) (|l#3@@26| Bool) ) (! (let ((alpha@@33 (FieldTypeInv0 (type $f@@26))))
 (=> (and (and (and (and (= (type $o@@36) refType) (= (type $f@@26) (FieldType alpha@@33))) (= (type |l#0@@28|) refType)) (= (type |l#1@@28|) (MapType0Type refType MapType1Type))) (= (type |l#2@@28|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#37| |l#0@@28| |l#1@@28| |l#2@@28| |l#3@@26|) $o@@36 $f@@26))  (=> (and (not (= $o@@36 |l#0@@28|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@28| $o@@36) |l#2@@28|))) |l#3@@26|))))
 :qid |SMNADTLi.325:17|
 :skolemid |1315|
 :pattern ( (MapType5Select (|lambda#37| |l#0@@28| |l#1@@28| |l#2@@28| |l#3@@26|) $o@@36 $f@@26))
)))
(assert (forall ((arg0@@250 T@U) (arg1@@136 T@U) (arg2@@82 T@U) (arg3@@57 Bool) ) (! (= (type (|lambda#38| arg0@@250 arg1@@136 arg2@@82 arg3@@57)) (MapType5Type refType boolType))
 :qid |funType:lambda#38|
 :pattern ( (|lambda#38| arg0@@250 arg1@@136 arg2@@82 arg3@@57))
)))
(assert (forall (($o@@37 T@U) ($f@@27 T@U) (|l#0@@29| T@U) (|l#1@@29| T@U) (|l#2@@29| T@U) (|l#3@@27| Bool) ) (! (let ((alpha@@34 (FieldTypeInv0 (type $f@@27))))
 (=> (and (and (and (and (= (type $o@@37) refType) (= (type $f@@27) (FieldType alpha@@34))) (= (type |l#0@@29|) refType)) (= (type |l#1@@29|) (MapType0Type refType MapType1Type))) (= (type |l#2@@29|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#38| |l#0@@29| |l#1@@29| |l#2@@29| |l#3@@27|) $o@@37 $f@@27))  (=> (and (not (= $o@@37 |l#0@@29|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@29| $o@@37) |l#2@@29|))) |l#3@@27|))))
 :qid |SMNADTLi.325:17|
 :skolemid |1316|
 :pattern ( (MapType5Select (|lambda#38| |l#0@@29| |l#1@@29| |l#2@@29| |l#3@@27|) $o@@37 $f@@27))
)))
(assert (forall ((arg0@@251 T@U) (arg1@@137 T@U) (arg2@@83 T@U) (arg3@@58 Bool) ) (! (= (type (|lambda#39| arg0@@251 arg1@@137 arg2@@83 arg3@@58)) (MapType5Type refType boolType))
 :qid |funType:lambda#39|
 :pattern ( (|lambda#39| arg0@@251 arg1@@137 arg2@@83 arg3@@58))
)))
(assert (forall (($o@@38 T@U) ($f@@28 T@U) (|l#0@@30| T@U) (|l#1@@30| T@U) (|l#2@@30| T@U) (|l#3@@28| Bool) ) (! (let ((alpha@@35 (FieldTypeInv0 (type $f@@28))))
 (=> (and (and (and (and (= (type $o@@38) refType) (= (type $f@@28) (FieldType alpha@@35))) (= (type |l#0@@30|) refType)) (= (type |l#1@@30|) (MapType0Type refType MapType1Type))) (= (type |l#2@@30|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#39| |l#0@@30| |l#1@@30| |l#2@@30| |l#3@@28|) $o@@38 $f@@28))  (=> (and (not (= $o@@38 |l#0@@30|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@30| $o@@38) |l#2@@30|))) |l#3@@28|))))
 :qid |SMNADTLi.355:7|
 :skolemid |1317|
 :pattern ( (MapType5Select (|lambda#39| |l#0@@30| |l#1@@30| |l#2@@30| |l#3@@28|) $o@@38 $f@@28))
)))
(assert (forall ((arg0@@252 T@U) (arg1@@138 T@U) (arg2@@84 T@U) (arg3@@59 Bool) ) (! (= (type (|lambda#40| arg0@@252 arg1@@138 arg2@@84 arg3@@59)) (MapType5Type refType boolType))
 :qid |funType:lambda#40|
 :pattern ( (|lambda#40| arg0@@252 arg1@@138 arg2@@84 arg3@@59))
)))
(assert (forall (($o@@39 T@U) ($f@@29 T@U) (|l#0@@31| T@U) (|l#1@@31| T@U) (|l#2@@31| T@U) (|l#3@@29| Bool) ) (! (let ((alpha@@36 (FieldTypeInv0 (type $f@@29))))
 (=> (and (and (and (and (= (type $o@@39) refType) (= (type $f@@29) (FieldType alpha@@36))) (= (type |l#0@@31|) refType)) (= (type |l#1@@31|) (MapType0Type refType MapType1Type))) (= (type |l#2@@31|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#40| |l#0@@31| |l#1@@31| |l#2@@31| |l#3@@29|) $o@@39 $f@@29))  (=> (and (not (= $o@@39 |l#0@@31|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@31| $o@@39) |l#2@@31|))) |l#3@@29|))))
 :qid |SMNADTLi.355:7|
 :skolemid |1318|
 :pattern ( (MapType5Select (|lambda#40| |l#0@@31| |l#1@@31| |l#2@@31| |l#3@@29|) $o@@39 $f@@29))
)))
(assert (forall ((arg0@@253 T@U) (arg1@@139 T@U) (arg2@@85 T@U) (arg3@@60 Bool) ) (! (= (type (|lambda#41| arg0@@253 arg1@@139 arg2@@85 arg3@@60)) (MapType5Type refType boolType))
 :qid |funType:lambda#41|
 :pattern ( (|lambda#41| arg0@@253 arg1@@139 arg2@@85 arg3@@60))
)))
(assert (forall (($o@@40 T@U) ($f@@30 T@U) (|l#0@@32| T@U) (|l#1@@32| T@U) (|l#2@@32| T@U) (|l#3@@30| Bool) ) (! (let ((alpha@@37 (FieldTypeInv0 (type $f@@30))))
 (=> (and (and (and (and (= (type $o@@40) refType) (= (type $f@@30) (FieldType alpha@@37))) (= (type |l#0@@32|) refType)) (= (type |l#1@@32|) (MapType0Type refType MapType1Type))) (= (type |l#2@@32|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#41| |l#0@@32| |l#1@@32| |l#2@@32| |l#3@@30|) $o@@40 $f@@30))  (=> (and (not (= $o@@40 |l#0@@32|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@32| $o@@40) |l#2@@32|))) |l#3@@30|))))
 :qid |SMNADTLi.419:17|
 :skolemid |1319|
 :pattern ( (MapType5Select (|lambda#41| |l#0@@32| |l#1@@32| |l#2@@32| |l#3@@30|) $o@@40 $f@@30))
)))
(assert (forall ((arg0@@254 T@U) (arg1@@140 T@U) (arg2@@86 T@U) (arg3@@61 Bool) ) (! (= (type (|lambda#42| arg0@@254 arg1@@140 arg2@@86 arg3@@61)) (MapType5Type refType boolType))
 :qid |funType:lambda#42|
 :pattern ( (|lambda#42| arg0@@254 arg1@@140 arg2@@86 arg3@@61))
)))
(assert (forall (($o@@41 T@U) ($f@@31 T@U) (|l#0@@33| T@U) (|l#1@@33| T@U) (|l#2@@33| T@U) (|l#3@@31| Bool) ) (! (let ((alpha@@38 (FieldTypeInv0 (type $f@@31))))
 (=> (and (and (and (and (= (type $o@@41) refType) (= (type $f@@31) (FieldType alpha@@38))) (= (type |l#0@@33|) refType)) (= (type |l#1@@33|) (MapType0Type refType MapType1Type))) (= (type |l#2@@33|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#42| |l#0@@33| |l#1@@33| |l#2@@33| |l#3@@31|) $o@@41 $f@@31))  (=> (and (not (= $o@@41 |l#0@@33|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@33| $o@@41) |l#2@@33|))) |l#3@@31|))))
 :qid |SMNADTLi.419:17|
 :skolemid |1320|
 :pattern ( (MapType5Select (|lambda#42| |l#0@@33| |l#1@@33| |l#2@@33| |l#3@@31|) $o@@41 $f@@31))
)))
(assert (forall ((arg0@@255 T@U) (arg1@@141 T@U) (arg2@@87 T@U) (arg3@@62 Bool) ) (! (= (type (|lambda#43| arg0@@255 arg1@@141 arg2@@87 arg3@@62)) (MapType5Type refType boolType))
 :qid |funType:lambda#43|
 :pattern ( (|lambda#43| arg0@@255 arg1@@141 arg2@@87 arg3@@62))
)))
(assert (forall (($o@@42 T@U) ($f@@32 T@U) (|l#0@@34| T@U) (|l#1@@34| T@U) (|l#2@@34| T@U) (|l#3@@32| Bool) ) (! (let ((alpha@@39 (FieldTypeInv0 (type $f@@32))))
 (=> (and (and (and (and (= (type $o@@42) refType) (= (type $f@@32) (FieldType alpha@@39))) (= (type |l#0@@34|) refType)) (= (type |l#1@@34|) (MapType0Type refType MapType1Type))) (= (type |l#2@@34|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#43| |l#0@@34| |l#1@@34| |l#2@@34| |l#3@@32|) $o@@42 $f@@32))  (=> (and (not (= $o@@42 |l#0@@34|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@34| $o@@42) |l#2@@34|))) |l#3@@32|))))
 :qid |SMNADTLi.449:7|
 :skolemid |1321|
 :pattern ( (MapType5Select (|lambda#43| |l#0@@34| |l#1@@34| |l#2@@34| |l#3@@32|) $o@@42 $f@@32))
)))
(assert (forall ((arg0@@256 T@U) (arg1@@142 T@U) (arg2@@88 T@U) (arg3@@63 Bool) ) (! (= (type (|lambda#44| arg0@@256 arg1@@142 arg2@@88 arg3@@63)) (MapType5Type refType boolType))
 :qid |funType:lambda#44|
 :pattern ( (|lambda#44| arg0@@256 arg1@@142 arg2@@88 arg3@@63))
)))
(assert (forall (($o@@43 T@U) ($f@@33 T@U) (|l#0@@35| T@U) (|l#1@@35| T@U) (|l#2@@35| T@U) (|l#3@@33| Bool) ) (! (let ((alpha@@40 (FieldTypeInv0 (type $f@@33))))
 (=> (and (and (and (and (= (type $o@@43) refType) (= (type $f@@33) (FieldType alpha@@40))) (= (type |l#0@@35|) refType)) (= (type |l#1@@35|) (MapType0Type refType MapType1Type))) (= (type |l#2@@35|) (FieldType boolType))) (= (U_2_bool (MapType5Select (|lambda#44| |l#0@@35| |l#1@@35| |l#2@@35| |l#3@@33|) $o@@43 $f@@33))  (=> (and (not (= $o@@43 |l#0@@35|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@35| $o@@43) |l#2@@35|))) |l#3@@33|))))
 :qid |SMNADTLi.449:7|
 :skolemid |1322|
 :pattern ( (MapType5Select (|lambda#44| |l#0@@35| |l#1@@35| |l#2@@35| |l#3@@33|) $o@@43 $f@@33))
)))
(declare-fun |xs#0@@49| () T@U)
(declare-fun |n#0@@40| () T@U)
(declare-fun |len#0@@26| () T@U)
(declare-fun $_Frame@0 () T@U)
(declare-fun TType () T@T)
(declare-fun type@@0 (T@U) T@U)
(declare-fun $Heap@1 () T@U)
(declare-fun $Heap@0 () T@U)
(declare-fun $Heap@2 () T@U)
(declare-fun |llen#0@0| () T@U)
(declare-fun |half#0@0| () T@U)
(declare-fun |L#0@0| () T@U)
(declare-fun $Heap@10 () T@U)
(declare-fun |s#1_0@0| () T@U)
(declare-fun $Heap@11 () T@U)
(declare-fun $Heap@12 () T@U)
(declare-fun $Heap@13 () T@U)
(declare-fun $Heap@14 () T@U)
(declare-fun $Heap@15 () T@U)
(declare-fun $Heap@16 () T@U)
(declare-fun |s#3@0| () T@U)
(declare-fun |x#6@0| () T@U)
(declare-fun $Heap@23 () T@U)
(declare-fun |A##2_0@0| () T@U)
(declare-fun |bound#0@0| () T@U)
(declare-fun $Heap@24 () T@U)
(declare-fun |##m#18@0| () T@U)
(declare-fun $Heap@17 () T@U)
(declare-fun $Heap@18 () T@U)
(declare-fun $Heap@19 () T@U)
(declare-fun $Heap@20 () T@U)
(declare-fun |R#0@0| () T@U)
(declare-fun |##n#15@0| () T@U)
(declare-fun |##len#2@0| () T@U)
(declare-fun |x##0@0| () T@U)
(declare-fun $Heap@21 () T@U)
(declare-fun |n##0@0| () T@U)
(declare-fun |len##0@0| () T@U)
(declare-fun $Heap@22 () T@U)
(declare-fun |##n#9@0| () T@U)
(declare-fun |##b#0@0| () T@U)
(declare-fun |let#1#0#0| () T@U)
(declare-fun |b##0@0| () T@U)
(declare-fun $Heap@3 () T@U)
(declare-fun $Heap@4 () T@U)
(declare-fun |A##0@0| () T@U)
(declare-fun $Heap@5 () T@U)
(declare-fun $Heap@6 () T@U)
(declare-fun $Heap@7 () T@U)
(declare-fun $Heap@8 () T@U)
(declare-fun $Heap@9 () T@U)
(declare-fun $Heap () T@U)
(declare-fun |half#0@@3| () T@U)
(declare-fun |llen#0@@5| () T@U)
(declare-fun |bound#0| () T@U)
(declare-fun |s#1_0| () T@U)
(declare-fun |s#3| () T@U)
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun %lbl%+2 () Bool)
(declare-fun %lbl%+3 () Bool)
(declare-fun %lbl%@4 () Bool)
(declare-fun $o@@44 () T@U)
(declare-fun $f@@34 () T@U)
(declare-fun %lbl%@5 () Bool)
(declare-fun %lbl%@6 () Bool)
(declare-fun $IsHeapAnchor (T@U) Bool)
(declare-fun %lbl%+7 () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun %lbl%+9 () Bool)
(declare-fun %lbl%+10 () Bool)
(declare-fun %lbl%+11 () Bool)
(declare-fun %lbl%+12 () Bool)
(declare-fun %lbl%+13 () Bool)
(declare-fun %lbl%@14 () Bool)
(declare-fun %lbl%@15 () Bool)
(declare-fun %lbl%@16 () Bool)
(declare-fun %lbl%@17 () Bool)
(declare-fun %lbl%+18 () Bool)
(declare-fun %lbl%+19 () Bool)
(declare-fun %lbl%@20 () Bool)
(declare-fun $o@@45 () T@U)
(declare-fun $f@@35 () T@U)
(declare-fun %lbl%@21 () Bool)
(declare-fun $o@@46 () T@U)
(declare-fun $f@@36 () T@U)
(declare-fun %lbl%@22 () Bool)
(declare-fun $o@@47 () T@U)
(declare-fun $f@@37 () T@U)
(declare-fun %lbl%@23 () Bool)
(declare-fun $o@@48 () T@U)
(declare-fun $f@@38 () T@U)
(declare-fun %lbl%@24 () Bool)
(declare-fun %lbl%@25 () Bool)
(declare-fun $o@@49 () T@U)
(declare-fun $f@@39 () T@U)
(declare-fun %lbl%@26 () Bool)
(declare-fun %lbl%@27 () Bool)
(declare-fun $o@@50 () T@U)
(declare-fun $f@@40 () T@U)
(declare-fun %lbl%@28 () Bool)
(declare-fun %lbl%@29 () Bool)
(declare-fun %lbl%@30 () Bool)
(declare-fun %lbl%@31 () Bool)
(declare-fun %lbl%@32 () Bool)
(declare-fun $o@@51 () T@U)
(declare-fun $f@@41 () T@U)
(declare-fun %lbl%+33 () Bool)
(declare-fun %lbl%@34 () Bool)
(declare-fun %lbl%@35 () Bool)
(declare-fun $o@@52 () T@U)
(declare-fun $f@@42 () T@U)
(declare-fun %lbl%@36 () Bool)
(declare-fun $o@@53 () T@U)
(declare-fun $f@@43 () T@U)
(declare-fun %lbl%@37 () Bool)
(declare-fun $o@@54 () T@U)
(declare-fun $f@@44 () T@U)
(declare-fun %lbl%@38 () Bool)
(declare-fun %lbl%@39 () Bool)
(declare-fun $o@@55 () T@U)
(declare-fun $f@@45 () T@U)
(declare-fun %lbl%@40 () Bool)
(declare-fun %lbl%@41 () Bool)
(declare-fun %lbl%@42 () Bool)
(declare-fun %lbl%@43 () Bool)
(declare-fun %lbl%@44 () Bool)
(declare-fun $o@@56 () T@U)
(declare-fun $f@@46 () T@U)
(declare-fun %lbl%@45 () Bool)
(declare-fun $o@@57 () T@U)
(declare-fun $f@@47 () T@U)
(declare-fun %lbl%+46 () Bool)
(declare-fun %lbl%@47 () Bool)
(declare-fun $o@@58 () T@U)
(declare-fun $f@@48 () T@U)
(declare-fun %lbl%@48 () Bool)
(declare-fun %lbl%@49 () Bool)
(declare-fun $o@@59 () T@U)
(declare-fun $f@@49 () T@U)
(declare-fun %lbl%@50 () Bool)
(declare-fun %lbl%@51 () Bool)
(declare-fun $o@@60 () T@U)
(declare-fun $f@@50 () T@U)
(declare-fun %lbl%@52 () Bool)
(declare-fun |a##0@0| () Int)
(declare-fun %lbl%@53 () Bool)
(declare-fun $o@@61 () T@U)
(declare-fun $f@@51 () T@U)
(declare-fun %lbl%@54 () Bool)
(declare-fun $o@@62 () T@U)
(declare-fun $f@@52 () T@U)
(declare-fun %lbl%@55 () Bool)
(declare-fun $o@@63 () T@U)
(declare-fun $f@@53 () T@U)
(declare-fun %lbl%@56 () Bool)
(declare-fun $o@@64 () T@U)
(declare-fun $f@@54 () T@U)
(declare-fun %lbl%@57 () Bool)
(declare-fun $o@@65 () T@U)
(declare-fun $f@@55 () T@U)
(declare-fun %lbl%+58 () Bool)
(declare-fun %lbl%@59 () Bool)
(declare-fun $o@@66 () T@U)
(declare-fun $f@@56 () T@U)
(declare-fun %lbl%@60 () Bool)
(declare-fun $o@@67 () T@U)
(declare-fun $f@@57 () T@U)
(declare-fun %lbl%+61 () Bool)
(declare-fun %lbl%+62 () Bool)
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type |xs#0@@49|) DatatypeTypeType) (= (type |n#0@@40|) BoxType)) (= (type |len#0@@26|) BoxType)) (= (type $_Frame@0) (MapType5Type refType boolType))) (= (Ctor TType) 27)) (forall ((arg0@@257 T@U) ) (! (= (type (type@@0 arg0@@257)) TType)
 :qid |funType:type|
 :pattern ( (type@@0 arg0@@257))
))) (= (type $Heap@1) (MapType0Type refType MapType1Type))) (= (type $Heap@0) (MapType0Type refType MapType1Type))) (= (type $Heap@2) (MapType0Type refType MapType1Type))) (= (type |llen#0@0|) BoxType)) (= (type |half#0@0|) BoxType)) (= (type |L#0@0|) DatatypeTypeType)) (= (type $Heap@10) (MapType0Type refType MapType1Type))) (= (type |s#1_0@0|) BoxType)) (= (type $Heap@11) (MapType0Type refType MapType1Type))) (= (type $Heap@12) (MapType0Type refType MapType1Type))) (= (type $Heap@13) (MapType0Type refType MapType1Type))) (= (type $Heap@14) (MapType0Type refType MapType1Type))) (= (type $Heap@15) (MapType0Type refType MapType1Type))) (= (type $Heap@16) (MapType0Type refType MapType1Type))) (= (type |s#3@0|) BoxType)) (= (type |x#6@0|) BoxType)) (= (type $Heap@23) (MapType0Type refType MapType1Type))) (= (type |A##2_0@0|) (MapType0Type BoxType boolType))) (= (type |bound#0@0|) (MapType0Type BoxType boolType))) (= (type $Heap@24) (MapType0Type refType MapType1Type))) (= (type |##m#18@0|) BoxType)) (= (type $Heap@17) (MapType0Type refType MapType1Type))) (= (type $Heap@18) (MapType0Type refType MapType1Type))) (= (type $Heap@19) (MapType0Type refType MapType1Type))) (= (type $Heap@20) (MapType0Type refType MapType1Type))) (= (type |R#0@0|) DatatypeTypeType)) (= (type |##n#15@0|) BoxType)) (= (type |##len#2@0|) BoxType)) (= (type |x##0@0|) BoxType)) (= (type $Heap@21) (MapType0Type refType MapType1Type))) (= (type |n##0@0|) BoxType)) (= (type |len##0@0|) BoxType)) (= (type $Heap@22) (MapType0Type refType MapType1Type))) (= (type |##n#9@0|) BoxType)) (= (type |##b#0@0|) BoxType)) (= (type |let#1#0#0|) DatatypeTypeType)) (= (type |b##0@0|) BoxType)) (= (type $Heap@3) (MapType0Type refType MapType1Type))) (= (type $Heap@4) (MapType0Type refType MapType1Type))) (= (type |A##0@0|) (MapType0Type BoxType boolType))) (= (type $Heap@5) (MapType0Type refType MapType1Type))) (= (type $Heap@6) (MapType0Type refType MapType1Type))) (= (type $Heap@7) (MapType0Type refType MapType1Type))) (= (type $Heap@8) (MapType0Type refType MapType1Type))) (= (type $Heap@9) (MapType0Type refType MapType1Type))) (= (type $Heap) (MapType0Type refType MapType1Type))) (= (type |half#0@@3|) BoxType)) (= (type |llen#0@@5|) BoxType)) (= (type |bound#0|) (MapType0Type BoxType boolType))) (= (type |s#1_0|) BoxType)) (= (type |s#3|) BoxType)))
(push 1)
(set-info :boogie-vc-id Impl$$_module.__default.SMN_k__Correct)
(assert (not
(let ((anon12_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1 (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |xs#0@@49|) |x#6@0|))) :lblneg @1))))
(let ((anon20_Else_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (not (_module.__default.AbLt |x#6@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|))) anon12_correct))))
(let ((anon20_Then_correct  (=> (! (and %lbl%+3 true) :lblpos +3) (=> (_module.__default.AbLt |x#6@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|)) (=> (and (and ($IsAlloc |L#0@0| (Tclass._module.List |#$AbInt|) $Heap@23) (|_module.__default.Elements#canCall| |L#0@0|)) (and (|_module.__default.Elements#canCall| |L#0@0|) (= |A##2_0@0| (_module.__default.Elements ($LS $LZ) |L#0@0|)))) (and (! (or %lbl%@4 (forall (($o@@68 T@U) ($f@@58 T@U) ) (! (let ((alpha@@41 (FieldTypeInv0 (type $f@@58))))
 (=> (and (and (= (type $o@@68) refType) (= (type $f@@58) (FieldType alpha@@41))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@68 $f@@58))))
 :qid |SMNADTLi.412:22|
 :skolemid |1226|
 :no-pattern (type $o@@68)
 :no-pattern (type $f@@58)
 :no-pattern (U_2_int $o@@68)
 :no-pattern (U_2_bool $o@@68)
 :no-pattern (U_2_int $f@@58)
 :no-pattern (U_2_bool $f@@58)
))) :lblneg @4) (=> (forall (($o@@69 T@U) ($f@@59 T@U) ) (! (let ((alpha@@42 (FieldTypeInv0 (type $f@@59))))
 (=> (and (and (= (type $o@@69) refType) (= (type $f@@59) (FieldType alpha@@42))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@69 $f@@59))))
 :qid |SMNADTLi.412:22|
 :skolemid |1226|
 :no-pattern (type@@0 $o@@44)
 :no-pattern (type@@0 $f@@34)
 :no-pattern (type $o@@69)
 :no-pattern (type $f@@59)
 :no-pattern (U_2_int $o@@69)
 :no-pattern (U_2_bool $o@@69)
 :no-pattern (U_2_int $f@@59)
 :no-pattern (U_2_bool $f@@59)
)) (and (! (or %lbl%@5 (|Set#Subset| |A##2_0@0| |bound#0@0|)) :lblneg @5) (=> (|Set#Subset| |A##2_0@0| |bound#0@0|) (and (! (or %lbl%@6 (= (_module.__default.AbSetLen |A##2_0@0|) (_module.__default.AbSetLen |bound#0@0|))) :lblneg @6) (=> (= (_module.__default.AbSetLen |A##2_0@0|) (_module.__default.AbSetLen |bound#0@0|)) (=> (and (and ($IsGoodHeap $Heap@24) ($IsHeapAnchor $Heap@24)) (and (|Set#Equal| |A##2_0@0| |bound#0@0|) (= $Heap@23 $Heap@24))) anon12_correct))))))))))))
(let ((anon9_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (and (|_module.__default.AbLt#canCall| |n#0@@40| |x#6@0|) (=> (or (_module.__default.AbLt |n#0@@40| |x#6@0|) (= |n#0@@40| |x#6@0|)) (|_module.__default.AbLt#canCall| |x#6@0| |s#3@0|))) (=> (and (and (or (_module.__default.AbLt |n#0@@40| |x#6@0|) (= |n#0@@40| |x#6@0|)) (_module.__default.AbLt |x#6@0| |s#3@0|)) ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@23)) (=> (and (and (and ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@23) (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|)) (and ($IsAllocBox |x#6@0| |#$AbInt| $Heap@23) (= |##m#18@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|)))) (and (and ($IsAllocBox |##m#18@0| |#$AbInt| $Heap@23) (|_module.__default.AbLt#canCall| |x#6@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|))) (and (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|) (|_module.__default.AbLt#canCall| |x#6@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|))))) (and anon20_Then_correct anon20_Else_correct)))))))
(let ((anon19_Else_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (not (or (_module.__default.AbLt |n#0@@40| |x#6@0|) (= |n#0@@40| |x#6@0|))) anon9_correct))))
(let ((anon19_Then_correct  (=> (! (and %lbl%+9 true) :lblpos +9) (=> (and (and (or (_module.__default.AbLt |n#0@@40| |x#6@0|) (= |n#0@@40| |x#6@0|)) ($IsAllocBox |x#6@0| |#$AbInt| $Heap@23)) (and ($IsAllocBox |s#3@0| |#$AbInt| $Heap@23) (|_module.__default.AbLt#canCall| |x#6@0| |s#3@0|))) anon9_correct))))
(let ((anon18_Else_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (_module.__default.AbLt |n#0@@40| |x#6@0|) (and anon19_Then_correct anon19_Else_correct)))))
(let ((anon18_Then_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (=> (not (_module.__default.AbLt |n#0@@40| |x#6@0|)) (and anon19_Then_correct anon19_Else_correct)))))
(let ((anon17_Then_correct  (=> (! (and %lbl%+12 true) :lblpos +12) (=> (and (and ($IsBox |x#6@0| |#$AbInt|) ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@23)) (and ($IsAllocBox |x#6@0| |#$AbInt| $Heap@23) (|_module.__default.AbLt#canCall| |n#0@@40| |x#6@0|))) (and anon18_Then_correct anon18_Else_correct)))))
(let ((GeneratedUnifiedExit_correct  (=> (! (and %lbl%+13 true) :lblpos +13) (and (! (or %lbl%@14 (let ((|s#1| (_module.__default.SMN_k ($LS ($LS $LZ)) |xs#0@@49| |n#0@@40| |len#0@@26|)))
 (or (_module.__default.AbLt |n#0@@40| |s#1|) (= |n#0@@40| |s#1|)))) :lblneg @14) (=> (let ((|s#1@@0| (_module.__default.SMN_k ($LS ($LS $LZ)) |xs#0@@49| |n#0@@40| |len#0@@26|)))
 (or (_module.__default.AbLt |n#0@@40| |s#1@@0|) (= |n#0@@40| |s#1@@0|))) (and (! (or %lbl%@15 (let ((|s#1@@1| (_module.__default.SMN_k ($LS ($LS $LZ)) |xs#0@@49| |n#0@@40| |len#0@@26|)))
 (or (_module.__default.AbLt |s#1@@1| (_module.__default.AbInc |n#0@@40| |len#0@@26|)) (= |s#1@@1| (_module.__default.AbInc |n#0@@40| |len#0@@26|))))) :lblneg @15) (=> (let ((|s#1@@2| (_module.__default.SMN_k ($LS ($LS $LZ)) |xs#0@@49| |n#0@@40| |len#0@@26|)))
 (or (_module.__default.AbLt |s#1@@2| (_module.__default.AbInc |n#0@@40| |len#0@@26|)) (= |s#1@@2| (_module.__default.AbInc |n#0@@40| |len#0@@26|)))) (and (! (or %lbl%@16 (let ((|s#1@@3| (_module.__default.SMN_k ($LS ($LS $LZ)) |xs#0@@49| |n#0@@40| |len#0@@26|)))
 (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |xs#0@@49|) |s#1@@3|))))) :lblneg @16) (=> (let ((|s#1@@4| (_module.__default.SMN_k ($LS ($LS $LZ)) |xs#0@@49| |n#0@@40| |len#0@@26|)))
 (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |xs#0@@49|) |s#1@@4|)))) (! (or %lbl%@17 (let ((|s#1@@5| (_module.__default.SMN_k ($LS ($LS $LZ)) |xs#0@@49| |n#0@@40| |len#0@@26|)))
(forall ((|x#3@@1| T@U) ) (!  (=> (and (and (= (type |x#3@@1|) BoxType) ($IsBox |x#3@@1| |#$AbInt|)) (and (or (_module.__default.AbLt |n#0@@40| |x#3@@1|) (= |n#0@@40| |x#3@@1|)) (_module.__default.AbLt |x#3@@1| |s#1@@5|))) (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |xs#0@@49|) |x#3@@1|)))
 :qid |SMNADTLi.363:12|
 :skolemid |1198|
 :pattern ( (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |xs#0@@49|) |x#3@@1|))
 :pattern ( (_module.__default.AbLt |x#3@@1| |s#1@@5|))
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#3@@1|))
)))) :lblneg @17))))))))))
(let ((anon17_Else_correct  (=> (! (and %lbl%+18 true) :lblpos +18) (=> (forall ((|x#7| T@U) ) (!  (=> (= (type |x#7|) BoxType) (=> (and ($IsBox |x#7| |#$AbInt|) (and (or (_module.__default.AbLt |n#0@@40| |x#7|) (= |n#0@@40| |x#7|)) (_module.__default.AbLt |x#7| |s#3@0|))) (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#7|))))
 :qid |SMNADTLi.408:14|
 :skolemid |1227|
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#7|))
 :pattern ( (_module.__default.AbLt |x#7| |s#3@0|))
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#7|))
)) GeneratedUnifiedExit_correct))))
(let ((anon16_Else_correct  (=> (! (and %lbl%+19 true) :lblpos +19) (=> (not (_module.__default.AbLt |llen#0@0| |half#0@0|)) (and (! (or %lbl%@20 (forall (($o@@70 T@U) ($f@@60 T@U) ) (! (let ((alpha@@43 (FieldTypeInv0 (type $f@@60))))
 (=> (and (and (= (type $o@@70) refType) (= (type $f@@60) (FieldType alpha@@43))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@70 $f@@60))))
 :qid |SMNADTLi.398:24|
 :skolemid |1219|
 :no-pattern (type $o@@70)
 :no-pattern (type $f@@60)
 :no-pattern (U_2_int $o@@70)
 :no-pattern (U_2_bool $o@@70)
 :no-pattern (U_2_int $f@@60)
 :no-pattern (U_2_bool $f@@60)
))) :lblneg @20) (=> (forall (($o@@71 T@U) ($f@@61 T@U) ) (! (let ((alpha@@44 (FieldTypeInv0 (type $f@@61))))
 (=> (and (and (= (type $o@@71) refType) (= (type $f@@61) (FieldType alpha@@44))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@71 $f@@61))))
 :qid |SMNADTLi.398:24|
 :skolemid |1219|
 :no-pattern (type@@0 $o@@45)
 :no-pattern (type@@0 $f@@35)
 :no-pattern (type $o@@71)
 :no-pattern (type $f@@61)
 :no-pattern (U_2_int $o@@71)
 :no-pattern (U_2_bool $o@@71)
 :no-pattern (U_2_int $f@@61)
 :no-pattern (U_2_bool $f@@61)
)) (=> (and (and (and ($IsGoodHeap $Heap@17) ($IsHeapAnchor $Heap@17)) (forall ((|x#1@@1| T@U) ) (!  (=> (and (= (type |x#1@@1|) BoxType) ($IsBox |x#1@@1| |#$AbInt|)) (and (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 0)) |x#1@@1|)) (=> (not (_module.__default.AbLt (_module.__default.int2adt (LitInt 0)) |x#1@@1|)) (|_module.__default.int2adt#canCall| (LitInt 0)))))
 :qid |SMNADTLi.42:18|
 :skolemid |958|
 :pattern ( (_module.__default.AbLt (_module.__default.int2adt 0) |x#1@@1|))
))) (and (forall ((|x#1@@2| T@U) ) (!  (=> (and (= (type |x#1@@2|) BoxType) ($IsBox |x#1@@2| |#$AbInt|)) (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 0)) |x#1@@2|) (= |x#1@@2| (_module.__default.int2adt (LitInt 0)))))
 :qid |SMNADTLi.42:18|
 :skolemid |959|
 :pattern ( (_module.__default.AbLt (_module.__default.int2adt 0) |x#1@@2|))
)) (= $Heap@10 $Heap@17))) (and (! (or %lbl%@21 (forall (($o@@72 T@U) ($f@@62 T@U) ) (! (let ((alpha@@45 (FieldTypeInv0 (type $f@@62))))
 (=> (and (and (= (type $o@@72) refType) (= (type $f@@62) (FieldType alpha@@45))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@72 $f@@62))))
 :qid |SMNADTLi.399:21|
 :skolemid |1220|
 :no-pattern (type $o@@72)
 :no-pattern (type $f@@62)
 :no-pattern (U_2_int $o@@72)
 :no-pattern (U_2_bool $o@@72)
 :no-pattern (U_2_int $f@@62)
 :no-pattern (U_2_bool $f@@62)
))) :lblneg @21) (=> (forall (($o@@73 T@U) ($f@@63 T@U) ) (! (let ((alpha@@46 (FieldTypeInv0 (type $f@@63))))
 (=> (and (and (= (type $o@@73) refType) (= (type $f@@63) (FieldType alpha@@46))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@73 $f@@63))))
 :qid |SMNADTLi.399:21|
 :skolemid |1220|
 :no-pattern (type@@0 $o@@46)
 :no-pattern (type@@0 $f@@36)
 :no-pattern (type $o@@73)
 :no-pattern (type $f@@63)
 :no-pattern (U_2_int $o@@73)
 :no-pattern (U_2_bool $o@@73)
 :no-pattern (U_2_int $f@@63)
 :no-pattern (U_2_bool $f@@63)
)) (=> (and (and (and ($IsGoodHeap $Heap@18) ($IsHeapAnchor $Heap@18)) (forall ((|x#1@@3| T@U) (|y#1| T@U) ) (!  (=> (and (and (= (type |x#1@@3|) BoxType) (= (type |y#1|) BoxType)) (and ($IsBox |x#1@@3| |#$AbInt|) ($IsBox |y#1| |#$AbInt|))) (and (|_module.__default.AbLt#canCall| |x#1@@3| |y#1|) (|_module.__default.AbLt#canCall| |y#1| |x#1@@3|)))
 :qid |SMNADTLi.52:18|
 :skolemid |970|
 :pattern ( (_module.__default.AbLt |y#1| |x#1@@3|))
 :pattern ( (_module.__default.AbLt |x#1@@3| |y#1|))
))) (and (forall ((|x#1@@4| T@U) (|y#1@@0| T@U) ) (!  (=> (and (and (= (type |x#1@@4|) BoxType) (= (type |y#1@@0|) BoxType)) (and ($IsBox |x#1@@4| |#$AbInt|) ($IsBox |y#1@@0| |#$AbInt|))) (and (=> (_module.__default.AbLt |x#1@@4| |y#1@@0|) (not (or (_module.__default.AbLt |y#1@@0| |x#1@@4|) (= |x#1@@4| |y#1@@0|)))) (=> (not (or (_module.__default.AbLt |y#1@@0| |x#1@@4|) (= |x#1@@4| |y#1@@0|))) (_module.__default.AbLt |x#1@@4| |y#1@@0|))))
 :qid |SMNADTLi.52:18|
 :skolemid |971|
 :pattern ( (_module.__default.AbLt |y#1@@0| |x#1@@4|))
 :pattern ( (_module.__default.AbLt |x#1@@4| |y#1@@0|))
)) (= $Heap@17 $Heap@18))) (and (! (or %lbl%@22 (forall (($o@@74 T@U) ($f@@64 T@U) ) (! (let ((alpha@@47 (FieldTypeInv0 (type $f@@64))))
 (=> (and (and (= (type $o@@74) refType) (= (type $f@@64) (FieldType alpha@@47))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@74 $f@@64))))
 :qid |SMNADTLi.400:21|
 :skolemid |1221|
 :no-pattern (type $o@@74)
 :no-pattern (type $f@@64)
 :no-pattern (U_2_int $o@@74)
 :no-pattern (U_2_bool $o@@74)
 :no-pattern (U_2_int $f@@64)
 :no-pattern (U_2_bool $f@@64)
))) :lblneg @22) (=> (forall (($o@@75 T@U) ($f@@65 T@U) ) (! (let ((alpha@@48 (FieldTypeInv0 (type $f@@65))))
 (=> (and (and (= (type $o@@75) refType) (= (type $f@@65) (FieldType alpha@@48))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@75 $f@@65))))
 :qid |SMNADTLi.400:21|
 :skolemid |1221|
 :no-pattern (type@@0 $o@@47)
 :no-pattern (type@@0 $f@@37)
 :no-pattern (type $o@@75)
 :no-pattern (type $f@@65)
 :no-pattern (U_2_int $o@@75)
 :no-pattern (U_2_bool $o@@75)
 :no-pattern (U_2_int $f@@65)
 :no-pattern (U_2_bool $f@@65)
)) (=> (and (and (and ($IsGoodHeap $Heap@19) ($IsHeapAnchor $Heap@19)) (forall ((|x#1@@5| T@U) ) (!  (=> (and (= (type |x#1@@5|) BoxType) ($IsBox |x#1@@5| |#$AbInt|)) (and (and (|_module.__default.int2adt#canCall| (LitInt 1)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 1)) |x#1@@5|)) (=> (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |x#1@@5|) (and (|_module.__default.AbDiv2#canCall| |x#1@@5|) (|_module.__default.AbPos#canCall| (_module.__default.AbDiv2 |x#1@@5|))))))
 :qid |SMNADTLi.92:18|
 :skolemid |1012|
 :pattern ( (_module.__default.AbDiv2 |x#1@@5|))
 :pattern ( (_module.__default.AbLt (_module.__default.int2adt 1) |x#1@@5|))
))) (and (forall ((|x#1@@6| T@U) ) (!  (=> (and (and (= (type |x#1@@6|) BoxType) ($IsBox |x#1@@6| |#$AbInt|)) (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |x#1@@6|)) (_module.__default.AbPos (_module.__default.AbDiv2 |x#1@@6|)))
 :qid |SMNADTLi.92:18|
 :skolemid |1013|
 :pattern ( (_module.__default.AbDiv2 |x#1@@6|))
 :pattern ( (_module.__default.AbLt (_module.__default.int2adt 1) |x#1@@6|))
)) (= $Heap@18 $Heap@19))) (and (! (or %lbl%@23 (forall (($o@@76 T@U) ($f@@66 T@U) ) (! (let ((alpha@@49 (FieldTypeInv0 (type $f@@66))))
 (=> (and (and (= (type $o@@76) refType) (= (type $f@@66) (FieldType alpha@@49))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@76 $f@@66))))
 :qid |SMNADTLi.401:21|
 :skolemid |1222|
 :no-pattern (type $o@@76)
 :no-pattern (type $f@@66)
 :no-pattern (U_2_int $o@@76)
 :no-pattern (U_2_bool $o@@76)
 :no-pattern (U_2_int $f@@66)
 :no-pattern (U_2_bool $f@@66)
))) :lblneg @23) (=> (forall (($o@@77 T@U) ($f@@67 T@U) ) (! (let ((alpha@@50 (FieldTypeInv0 (type $f@@67))))
 (=> (and (and (= (type $o@@77) refType) (= (type $f@@67) (FieldType alpha@@50))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@77 $f@@67))))
 :qid |SMNADTLi.401:21|
 :skolemid |1222|
 :no-pattern (type@@0 $o@@48)
 :no-pattern (type@@0 $f@@38)
 :no-pattern (type $o@@77)
 :no-pattern (type $f@@67)
 :no-pattern (U_2_int $o@@77)
 :no-pattern (U_2_bool $o@@77)
 :no-pattern (U_2_int $f@@67)
 :no-pattern (U_2_bool $f@@67)
)) (=> (and (and (and (and ($IsGoodHeap $Heap@20) ($IsHeapAnchor $Heap@20)) (and (forall ((|x#1@@7| T@U) (|y#1@@1| T@U) (|z#1| T@U) ) (!  (=> (and (and (and (= (type |x#1@@7|) BoxType) (= (type |y#1@@1|) BoxType)) (= (type |z#1|) BoxType)) (and (and ($IsBox |x#1@@7| |#$AbInt|) ($IsBox |y#1@@1| |#$AbInt|)) ($IsBox |z#1| |#$AbInt|))) (and (and (|_module.__default.AbInc#canCall| |x#1@@7| |y#1@@1|) (=> (= (_module.__default.AbInc |x#1@@7| |y#1@@1|) |z#1|) (|_module.__default.AbDec#canCall| |z#1| |x#1@@7|))) (=> (=> (= (_module.__default.AbInc |x#1@@7| |y#1@@1|) |z#1|) (= (_module.__default.AbDec |z#1| |x#1@@7|) |y#1@@1|)) (and (|_module.__default.AbInc#canCall| |x#1@@7| |y#1@@1|) (=> (= (_module.__default.AbInc |x#1@@7| |y#1@@1|) |z#1|) (|_module.__default.AbDec#canCall| |z#1| |y#1@@1|))))))
 :qid |SMNADTLi.54:18|
 :skolemid |973|
 :pattern ( (_module.__default.AbDec |z#1| |y#1@@1|) (_module.__default.AbDec |z#1| |x#1@@7|))
 :pattern ( (_module.__default.AbDec |z#1| |x#1@@7|) (_module.__default.AbInc |x#1@@7| |y#1@@1|))
)) (forall ((|x#1@@8| T@U) (|y#1@@2| T@U) (|z#1@@0| T@U) ) (!  (=> (and (and (and (= (type |x#1@@8|) BoxType) (= (type |y#1@@2|) BoxType)) (= (type |z#1@@0|) BoxType)) (and (and ($IsBox |x#1@@8| |#$AbInt|) ($IsBox |y#1@@2| |#$AbInt|)) ($IsBox |z#1@@0| |#$AbInt|))) (and (=> (= (_module.__default.AbInc |x#1@@8| |y#1@@2|) |z#1@@0|) (= (_module.__default.AbDec |z#1@@0| |x#1@@8|) |y#1@@2|)) (=> (= (_module.__default.AbInc |x#1@@8| |y#1@@2|) |z#1@@0|) (= (_module.__default.AbDec |z#1@@0| |y#1@@2|) |x#1@@8|))))
 :qid |SMNADTLi.54:18|
 :skolemid |974|
 :pattern ( (_module.__default.AbDec |z#1@@0| |y#1@@2|) (_module.__default.AbDec |z#1@@0| |x#1@@8|))
 :pattern ( (_module.__default.AbDec |z#1@@0| |x#1@@8|) (_module.__default.AbInc |x#1@@8| |y#1@@2|))
)))) (and (and (= $Heap@19 $Heap@20) ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@20)) (and ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@20) (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|)))) (and (and (and ($IsAllocBox |len#0@@26| |#$AbInt| $Heap@20) ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@20)) (and (|_module.__default.AbDec#canCall| |len#0@@26| |llen#0@0|) ($IsAlloc |R#0@0| (Tclass._module.List |#$AbInt|) $Heap@20))) (and (and (= |##n#15@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|)) ($IsAllocBox |##n#15@0| |#$AbInt| $Heap@20)) (and (= |##len#2@0| (_module.__default.AbDec |len#0@@26| |llen#0@0|)) ($IsAllocBox |##len#2@0| |#$AbInt| $Heap@20))))) (and (! (or %lbl%@24 (= |##len#2@0| (_module.__default.Length ($LS ($LS $LZ)) |R#0@0|))) :lblneg @24) (=> (and (= |##len#2@0| (_module.__default.Length ($LS $LZ) |R#0@0|)) (|_module.__default.SMN_k#canCall| |R#0@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|) (_module.__default.AbDec |len#0@@26| |llen#0@0|))) (=> (and (and (and (and (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|) (|_module.__default.AbDec#canCall| |len#0@@26| |llen#0@0|)) (|_module.__default.SMN_k#canCall| |R#0@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|) (_module.__default.AbDec |len#0@@26| |llen#0@0|))) (and (= |s#3@0| (_module.__default.SMN_k ($LS $LZ) |R#0@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|) (_module.__default.AbDec |len#0@@26| |llen#0@0|))) ($IsAllocBox |len#0@@26| |#$AbInt| $Heap@20))) (and (and ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@20) (|_module.__default.AbDec#canCall| |len#0@@26| |llen#0@0|)) (and (|_module.__default.AbDec#canCall| |len#0@@26| |llen#0@0|) (= |x##0@0| (_module.__default.AbDec |len#0@@26| |llen#0@0|))))) (and (! (or %lbl%@25 (forall (($o@@78 T@U) ($f@@68 T@U) ) (! (let ((alpha@@51 (FieldTypeInv0 (type $f@@68))))
 (=> (and (and (= (type $o@@78) refType) (= (type $f@@68) (FieldType alpha@@51))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@78 $f@@68))))
 :qid |SMNADTLi.403:23|
 :skolemid |1223|
 :no-pattern (type $o@@78)
 :no-pattern (type $f@@68)
 :no-pattern (U_2_int $o@@78)
 :no-pattern (U_2_bool $o@@78)
 :no-pattern (U_2_int $f@@68)
 :no-pattern (U_2_bool $f@@68)
))) :lblneg @25) (=> (forall (($o@@79 T@U) ($f@@69 T@U) ) (! (let ((alpha@@52 (FieldTypeInv0 (type $f@@69))))
 (=> (and (and (= (type $o@@79) refType) (= (type $f@@69) (FieldType alpha@@52))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@79 $f@@69))))
 :qid |SMNADTLi.403:23|
 :skolemid |1223|
 :no-pattern (type@@0 $o@@49)
 :no-pattern (type@@0 $f@@39)
 :no-pattern (type $o@@79)
 :no-pattern (type $f@@69)
 :no-pattern (U_2_int $o@@79)
 :no-pattern (U_2_bool $o@@79)
 :no-pattern (U_2_int $f@@69)
 :no-pattern (U_2_bool $f@@69)
)) (and (! (or %lbl%@26 (_module.__default.AbLt |x##0@0| |len#0@@26|)) :lblneg @26) (=> (_module.__default.AbLt |x##0@0| |len#0@@26|) (=> (and (and (and (and ($IsGoodHeap $Heap@21) ($IsHeapAnchor $Heap@21)) (and (|_module.__default.adt2dt#canCall| |x##0@0|) (|_module.__default.adt2dt#canCall| |len#0@@26|))) (and (and (< (DtRank (_module.__default.adt2dt |x##0@0|)) (DtRank (_module.__default.adt2dt |len#0@@26|))) (= $Heap@20 $Heap@21)) (and ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@21) ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@21)))) (and (and (and (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|) (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|)) (and (= |n##0@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|)) ($IsAllocBox |len#0@@26| |#$AbInt| $Heap@21))) (and (and ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@21) (|_module.__default.AbDec#canCall| |len#0@@26| |llen#0@0|)) (and (|_module.__default.AbDec#canCall| |len#0@@26| |llen#0@0|) (= |len##0@0| (_module.__default.AbDec |len#0@@26| |llen#0@0|)))))) (and (! (or %lbl%@27 (forall (($o@@80 T@U) ($f@@70 T@U) ) (! (let ((alpha@@53 (FieldTypeInv0 (type $f@@70))))
 (=> (and (and (= (type $o@@80) refType) (= (type $f@@70) (FieldType alpha@@53))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@80 $f@@70))))
 :qid |SMNADTLi.404:19|
 :skolemid |1224|
 :no-pattern (type $o@@80)
 :no-pattern (type $f@@70)
 :no-pattern (U_2_int $o@@80)
 :no-pattern (U_2_bool $o@@80)
 :no-pattern (U_2_int $f@@70)
 :no-pattern (U_2_bool $f@@70)
))) :lblneg @27) (=> (forall (($o@@81 T@U) ($f@@71 T@U) ) (! (let ((alpha@@54 (FieldTypeInv0 (type $f@@71))))
 (=> (and (and (= (type $o@@81) refType) (= (type $f@@71) (FieldType alpha@@54))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@81 $f@@71))))
 :qid |SMNADTLi.404:19|
 :skolemid |1224|
 :no-pattern (type@@0 $o@@50)
 :no-pattern (type@@0 $f@@40)
 :no-pattern (type $o@@81)
 :no-pattern (type $f@@71)
 :no-pattern (U_2_int $o@@81)
 :no-pattern (U_2_bool $o@@81)
 :no-pattern (U_2_int $f@@71)
 :no-pattern (U_2_bool $f@@71)
)) (and (! (or %lbl%@28 (< (DtRank (_module.__default.adt2dt |len##0@0|)) (DtRank (_module.__default.adt2dt |len#0@@26|)))) :lblneg @28) (=> (< (DtRank (_module.__default.adt2dt |len##0@0|)) (DtRank (_module.__default.adt2dt |len#0@@26|))) (and (! (or %lbl%@29 (_module.__default.NoDuplicates ($LS ($LS $LZ)) |R#0@0|)) :lblneg @29) (=> (_module.__default.NoDuplicates ($LS ($LS $LZ)) |R#0@0|) (and (! (or %lbl%@30 (forall ((|x#1@@9| T@U) ) (!  (=> (and (and (= (type |x#1@@9|) BoxType) ($IsBox |x#1@@9| |#$AbInt|)) (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |R#0@0|) |x#1@@9|))) (or (_module.__default.AbLt |n##0@0| |x#1@@9|) (= |n##0@0| |x#1@@9|)))
 :qid |SMNADTLi.357:19|
 :skolemid |1190|
 :pattern ( (_module.__default.AbLt |n##0@0| |x#1@@9|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |R#0@0|) |x#1@@9|))
))) :lblneg @30) (=> (forall ((|x#1@@10| T@U) ) (!  (=> (and (and (= (type |x#1@@10|) BoxType) ($IsBox |x#1@@10| |#$AbInt|)) (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |R#0@0|) |x#1@@10|))) (or (_module.__default.AbLt |n##0@0| |x#1@@10|) (= |n##0@0| |x#1@@10|)))
 :qid |SMNADTLi.357:19|
 :skolemid |1190|
 :pattern ( (_module.__default.AbLt |n##0@0| |x#1@@10|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |R#0@0|) |x#1@@10|))
)) (and (! (or %lbl%@31 (= |len##0@0| (_module.__default.Length ($LS ($LS $LZ)) |R#0@0|))) :lblneg @31) (=> (= |len##0@0| (_module.__default.Length ($LS ($LS $LZ)) |R#0@0|)) (=> (and ($IsGoodHeap $Heap@22) ($IsHeapAnchor $Heap@22)) (=> (and (and (and (|_module.__default.SMN_k#canCall| |R#0@0| |n##0@0| |len##0@0|) (let ((|s#1@@6| (_module.__default.SMN_k ($LS $LZ) |R#0@0| |n##0@0| |len##0@0|)))
 (and (|_module.__default.AbLt#canCall| |n##0@0| |s#1@@6|) (=> (or (_module.__default.AbLt |n##0@0| |s#1@@6|) (= |n##0@0| |s#1@@6|)) (and (and (and (|_module.__default.AbInc#canCall| |n##0@0| |len##0@0|) (|_module.__default.AbLt#canCall| |s#1@@6| (_module.__default.AbInc |n##0@0| |len##0@0|))) (=> (not (_module.__default.AbLt |s#1@@6| (_module.__default.AbInc |n##0@0| |len##0@0|))) (|_module.__default.AbInc#canCall| |n##0@0| |len##0@0|))) (=> (or (_module.__default.AbLt |s#1@@6| (_module.__default.AbInc |n##0@0| |len##0@0|)) (= |s#1@@6| (_module.__default.AbInc |n##0@0| |len##0@0|))) (and (|_module.__default.Elements#canCall| |R#0@0|) (=> (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |R#0@0|) |s#1@@6|))) (forall ((|x#3@@2| T@U) ) (!  (=> (and (= (type |x#3@@2|) BoxType) ($IsBox |x#3@@2| |#$AbInt|)) (and (|_module.__default.AbLt#canCall| |n##0@0| |x#3@@2|) (=> (or (_module.__default.AbLt |n##0@0| |x#3@@2|) (= |n##0@0| |x#3@@2|)) (and (|_module.__default.AbLt#canCall| |x#3@@2| |s#1@@6|) (=> (_module.__default.AbLt |x#3@@2| |s#1@@6|) (|_module.__default.Elements#canCall| |R#0@0|))))))
 :qid |SMNADTLi.363:12|
 :skolemid |1192|
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |R#0@0|) |x#3@@2|))
 :pattern ( (_module.__default.AbLt |x#3@@2| |s#1@@6|))
 :pattern ( (_module.__default.AbLt |n##0@0| |x#3@@2|))
)))))))))) (let ((|s#1@@7| (_module.__default.SMN_k ($LS ($LS $LZ)) |R#0@0| |n##0@0| |len##0@0|)))
 (or (_module.__default.AbLt |n##0@0| |s#1@@7|) (= |n##0@0| |s#1@@7|)))) (and (and (let ((|s#1@@8| (_module.__default.SMN_k ($LS ($LS $LZ)) |R#0@0| |n##0@0| |len##0@0|)))
 (or (_module.__default.AbLt |s#1@@8| (_module.__default.AbInc |n##0@0| |len##0@0|)) (= |s#1@@8| (_module.__default.AbInc |n##0@0| |len##0@0|)))) (let ((|s#1@@9| (_module.__default.SMN_k ($LS ($LS $LZ)) |R#0@0| |n##0@0| |len##0@0|)))
 (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |R#0@0|) |s#1@@9|))))) (and (let ((|s#1@@10| (_module.__default.SMN_k ($LS ($LS $LZ)) |R#0@0| |n##0@0| |len##0@0|)))
(forall ((|x#3@@3| T@U) ) (!  (=> (and (and (= (type |x#3@@3|) BoxType) ($IsBox |x#3@@3| |#$AbInt|)) (and (or (_module.__default.AbLt |n##0@0| |x#3@@3|) (= |n##0@0| |x#3@@3|)) (_module.__default.AbLt |x#3@@3| |s#1@@10|))) (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |R#0@0|) |x#3@@3|)))
 :qid |SMNADTLi.363:12|
 :skolemid |1194|
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |R#0@0|) |x#3@@3|))
 :pattern ( (_module.__default.AbLt |x#3@@3| |s#1@@10|))
 :pattern ( (_module.__default.AbLt |n##0@0| |x#3@@3|))
))) (= $Heap@21 $Heap@22)))) (and (! (or %lbl%@32 (forall (($o@@82 T@U) ($f@@72 T@U) ) (! (let ((alpha@@55 (FieldTypeInv0 (type $f@@72))))
 (=> (and (and (= (type $o@@82) refType) (= (type $f@@72) (FieldType alpha@@55))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@82 $f@@72))))
 :qid |SMNADTLi.407:33|
 :skolemid |1225|
 :no-pattern (type $o@@82)
 :no-pattern (type $f@@72)
 :no-pattern (U_2_int $o@@82)
 :no-pattern (U_2_bool $o@@82)
 :no-pattern (U_2_int $f@@72)
 :no-pattern (U_2_bool $f@@72)
))) :lblneg @32) (=> (forall (($o@@83 T@U) ($f@@73 T@U) ) (! (let ((alpha@@56 (FieldTypeInv0 (type $f@@73))))
 (=> (and (and (= (type $o@@83) refType) (= (type $f@@73) (FieldType alpha@@56))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@83 $f@@73))))
 :qid |SMNADTLi.407:33|
 :skolemid |1225|
 :no-pattern (type@@0 $o@@51)
 :no-pattern (type@@0 $f@@41)
 :no-pattern (type $o@@83)
 :no-pattern (type $f@@73)
 :no-pattern (U_2_int $o@@83)
 :no-pattern (U_2_bool $o@@83)
 :no-pattern (U_2_int $f@@73)
 :no-pattern (U_2_bool $f@@73)
)) (=> (and ($IsGoodHeap $Heap@23) ($IsHeapAnchor $Heap@23)) (=> (and (and (and (and (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|) (|_module.__default.AbDec#canCall| |len#0@@26| |llen#0@0|)) (|_module.__default.AbInc#canCall| (_module.__default.AbInc |n#0@@40| |llen#0@0|) (_module.__default.AbDec |len#0@@26| |llen#0@0|))) (|_module.__default.AbInc#canCall| |n#0@@40| |len#0@@26|)) (and (= (_module.__default.AbInc (_module.__default.AbInc |n#0@@40| |llen#0@0|) (_module.__default.AbDec |len#0@@26| |llen#0@0|)) (_module.__default.AbInc |n#0@@40| |len#0@@26|)) (= $Heap@22 $Heap@23))) (and anon17_Then_correct anon17_Else_correct)))))))))))))))))))))))))))))))))))))))))
(let ((anon16_Then_correct  (=> (! (and %lbl%+33 true) :lblpos +33) (=> (and (and (_module.__default.AbLt |llen#0@0| |half#0@0|) ($IsAlloc |L#0@0| (Tclass._module.List |#$AbInt|) $Heap@10)) (and ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@10) ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@10))) (and (! (or %lbl%@34 (= |llen#0@0| (_module.__default.Length ($LS ($LS $LZ)) |L#0@0|))) :lblneg @34) (=> (and (and (= |llen#0@0| (_module.__default.Length ($LS $LZ) |L#0@0|)) (|_module.__default.SMN_k#canCall| |L#0@0| |n#0@@40| |llen#0@0|)) (and (|_module.__default.SMN_k#canCall| |L#0@0| |n#0@@40| |llen#0@0|) (= |s#1_0@0| (_module.__default.SMN_k ($LS $LZ) |L#0@0| |n#0@@40| |llen#0@0|)))) (and (! (or %lbl%@35 (forall (($o@@84 T@U) ($f@@74 T@U) ) (! (let ((alpha@@57 (FieldTypeInv0 (type $f@@74))))
 (=> (and (and (= (type $o@@84) refType) (= (type $f@@74) (FieldType alpha@@57))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@84 $f@@74))))
 :qid |SMNADTLi.387:31|
 :skolemid |1213|
 :no-pattern (type $o@@84)
 :no-pattern (type $f@@74)
 :no-pattern (U_2_int $o@@84)
 :no-pattern (U_2_bool $o@@84)
 :no-pattern (U_2_int $f@@74)
 :no-pattern (U_2_bool $f@@74)
))) :lblneg @35) (=> (forall (($o@@85 T@U) ($f@@75 T@U) ) (! (let ((alpha@@58 (FieldTypeInv0 (type $f@@75))))
 (=> (and (and (= (type $o@@85) refType) (= (type $f@@75) (FieldType alpha@@58))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@85 $f@@75))))
 :qid |SMNADTLi.387:31|
 :skolemid |1213|
 :no-pattern (type@@0 $o@@52)
 :no-pattern (type@@0 $f@@42)
 :no-pattern (type $o@@85)
 :no-pattern (type $f@@75)
 :no-pattern (U_2_int $o@@85)
 :no-pattern (U_2_bool $o@@85)
 :no-pattern (U_2_int $f@@75)
 :no-pattern (U_2_bool $f@@75)
)) (=> (and ($IsGoodHeap $Heap@11) ($IsHeapAnchor $Heap@11)) (=> (and (and (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 0)) |len#0@@26|)) (and (and (|_module.__default.int2adt#canCall| (LitInt 1)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 1)) |len#0@@26|)) (=> (not (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |len#0@@26|)) (|_module.__default.int2adt#canCall| (LitInt 1))))) (and (and (=> (_module.__default.AbLt (_module.__default.int2adt (LitInt 0)) |len#0@@26|) (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |len#0@@26|) (= |len#0@@26| (_module.__default.int2adt (LitInt 1))))) (=> (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |len#0@@26|) (= |len#0@@26| (_module.__default.int2adt (LitInt 1)))) (_module.__default.AbLt (_module.__default.int2adt (LitInt 0)) |len#0@@26|))) (= $Heap@10 $Heap@11))) (and (! (or %lbl%@36 (forall (($o@@86 T@U) ($f@@76 T@U) ) (! (let ((alpha@@59 (FieldTypeInv0 (type $f@@76))))
 (=> (and (and (= (type $o@@86) refType) (= (type $f@@76) (FieldType alpha@@59))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@86 $f@@76))))
 :qid |SMNADTLi.388:35|
 :skolemid |1214|
 :no-pattern (type $o@@86)
 :no-pattern (type $f@@76)
 :no-pattern (U_2_int $o@@86)
 :no-pattern (U_2_bool $o@@86)
 :no-pattern (U_2_int $f@@76)
 :no-pattern (U_2_bool $f@@76)
))) :lblneg @36) (=> (forall (($o@@87 T@U) ($f@@77 T@U) ) (! (let ((alpha@@60 (FieldTypeInv0 (type $f@@77))))
 (=> (and (and (= (type $o@@87) refType) (= (type $f@@77) (FieldType alpha@@60))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@87 $f@@77))))
 :qid |SMNADTLi.388:35|
 :skolemid |1214|
 :no-pattern (type@@0 $o@@53)
 :no-pattern (type@@0 $f@@43)
 :no-pattern (type $o@@87)
 :no-pattern (type $f@@77)
 :no-pattern (U_2_int $o@@87)
 :no-pattern (U_2_bool $o@@87)
 :no-pattern (U_2_int $f@@77)
 :no-pattern (U_2_bool $f@@77)
)) (=> (and ($IsGoodHeap $Heap@12) ($IsHeapAnchor $Heap@12)) (=> (and (and (and (and (|_module.__default.int2adt#canCall| (LitInt 1)) (|_module.__default.AbLt#canCall| (_module.__default.int2adt (LitInt 1)) |len#0@@26|)) (=> (not (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |len#0@@26|)) (|_module.__default.int2adt#canCall| (LitInt 1)))) (=> (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |len#0@@26|) (= |len#0@@26| (_module.__default.int2adt (LitInt 1)))) (and (and (and (|_module.__default.AbInc1#canCall| |len#0@@26|) (|_module.__default.AbDiv2#canCall| (_module.__default.AbInc1 |len#0@@26|))) (|_module.__default.AbLt#canCall| (_module.__default.AbDiv2 (_module.__default.AbInc1 |len#0@@26|)) |len#0@@26|)) (=> (not (_module.__default.AbLt (_module.__default.AbDiv2 (_module.__default.AbInc1 |len#0@@26|)) |len#0@@26|)) (and (|_module.__default.AbInc1#canCall| |len#0@@26|) (|_module.__default.AbDiv2#canCall| (_module.__default.AbInc1 |len#0@@26|))))))) (and (=> (or (_module.__default.AbLt (_module.__default.int2adt (LitInt 1)) |len#0@@26|) (= |len#0@@26| (_module.__default.int2adt (LitInt 1)))) (or (_module.__default.AbLt (_module.__default.AbDiv2 (_module.__default.AbInc1 |len#0@@26|)) |len#0@@26|) (= (_module.__default.AbDiv2 (_module.__default.AbInc1 |len#0@@26|)) |len#0@@26|))) (= $Heap@11 $Heap@12))) (and (! (or %lbl%@37 (forall (($o@@88 T@U) ($f@@78 T@U) ) (! (let ((alpha@@61 (FieldTypeInv0 (type $f@@78))))
 (=> (and (and (= (type $o@@88) refType) (= (type $f@@78) (FieldType alpha@@61))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@88 $f@@78))))
 :qid |SMNADTLi.389:23|
 :skolemid |1215|
 :no-pattern (type $o@@88)
 :no-pattern (type $f@@78)
 :no-pattern (U_2_int $o@@88)
 :no-pattern (U_2_bool $o@@88)
 :no-pattern (U_2_int $f@@78)
 :no-pattern (U_2_bool $f@@78)
))) :lblneg @37) (=> (forall (($o@@89 T@U) ($f@@79 T@U) ) (! (let ((alpha@@62 (FieldTypeInv0 (type $f@@79))))
 (=> (and (and (= (type $o@@89) refType) (= (type $f@@79) (FieldType alpha@@62))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@89 $f@@79))))
 :qid |SMNADTLi.389:23|
 :skolemid |1215|
 :no-pattern (type@@0 $o@@54)
 :no-pattern (type@@0 $f@@44)
 :no-pattern (type $o@@89)
 :no-pattern (type $f@@79)
 :no-pattern (U_2_int $o@@89)
 :no-pattern (U_2_bool $o@@89)
 :no-pattern (U_2_int $f@@79)
 :no-pattern (U_2_bool $f@@79)
)) (and (! (or %lbl%@38 (_module.__default.AbLt |llen#0@0| |len#0@@26|)) :lblneg @38) (=> (_module.__default.AbLt |llen#0@0| |len#0@@26|) (=> (and ($IsGoodHeap $Heap@13) ($IsHeapAnchor $Heap@13)) (=> (and (and (|_module.__default.adt2dt#canCall| |llen#0@0|) (|_module.__default.adt2dt#canCall| |len#0@@26|)) (and (< (DtRank (_module.__default.adt2dt |llen#0@0|)) (DtRank (_module.__default.adt2dt |len#0@@26|))) (= $Heap@12 $Heap@13))) (and (! (or %lbl%@39 (forall (($o@@90 T@U) ($f@@80 T@U) ) (! (let ((alpha@@63 (FieldTypeInv0 (type $f@@80))))
 (=> (and (and (= (type $o@@90) refType) (= (type $f@@80) (FieldType alpha@@63))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@90 $f@@80))))
 :qid |SMNADTLi.390:19|
 :skolemid |1216|
 :no-pattern (type $o@@90)
 :no-pattern (type $f@@80)
 :no-pattern (U_2_int $o@@90)
 :no-pattern (U_2_bool $o@@90)
 :no-pattern (U_2_int $f@@80)
 :no-pattern (U_2_bool $f@@80)
))) :lblneg @39) (=> (forall (($o@@91 T@U) ($f@@81 T@U) ) (! (let ((alpha@@64 (FieldTypeInv0 (type $f@@81))))
 (=> (and (and (= (type $o@@91) refType) (= (type $f@@81) (FieldType alpha@@64))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@91 $f@@81))))
 :qid |SMNADTLi.390:19|
 :skolemid |1216|
 :no-pattern (type@@0 $o@@55)
 :no-pattern (type@@0 $f@@45)
 :no-pattern (type $o@@91)
 :no-pattern (type $f@@81)
 :no-pattern (U_2_int $o@@91)
 :no-pattern (U_2_bool $o@@91)
 :no-pattern (U_2_int $f@@81)
 :no-pattern (U_2_bool $f@@81)
)) (and (! (or %lbl%@40 (< (DtRank (_module.__default.adt2dt |llen#0@0|)) (DtRank (_module.__default.adt2dt |len#0@@26|)))) :lblneg @40) (=> (< (DtRank (_module.__default.adt2dt |llen#0@0|)) (DtRank (_module.__default.adt2dt |len#0@@26|))) (and (! (or %lbl%@41 (_module.__default.NoDuplicates ($LS ($LS $LZ)) |L#0@0|)) :lblneg @41) (=> (_module.__default.NoDuplicates ($LS ($LS $LZ)) |L#0@0|) (and (! (or %lbl%@42 (forall ((|x#1@@11| T@U) ) (!  (=> (and (and (= (type |x#1@@11|) BoxType) ($IsBox |x#1@@11| |#$AbInt|)) (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |L#0@0|) |x#1@@11|))) (or (_module.__default.AbLt |n#0@@40| |x#1@@11|) (= |n#0@@40| |x#1@@11|)))
 :qid |SMNADTLi.357:19|
 :skolemid |1190|
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#1@@11|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |L#0@0|) |x#1@@11|))
))) :lblneg @42) (=> (forall ((|x#1@@12| T@U) ) (!  (=> (and (and (= (type |x#1@@12|) BoxType) ($IsBox |x#1@@12| |#$AbInt|)) (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |L#0@0|) |x#1@@12|))) (or (_module.__default.AbLt |n#0@@40| |x#1@@12|) (= |n#0@@40| |x#1@@12|)))
 :qid |SMNADTLi.357:19|
 :skolemid |1190|
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#1@@12|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |L#0@0|) |x#1@@12|))
)) (and (! (or %lbl%@43 (= |llen#0@0| (_module.__default.Length ($LS ($LS $LZ)) |L#0@0|))) :lblneg @43) (=> (= |llen#0@0| (_module.__default.Length ($LS ($LS $LZ)) |L#0@0|)) (=> (and ($IsGoodHeap $Heap@14) ($IsHeapAnchor $Heap@14)) (=> (and (and (and (|_module.__default.SMN_k#canCall| |L#0@0| |n#0@@40| |llen#0@0|) (let ((|s#1@@11| (_module.__default.SMN_k ($LS $LZ) |L#0@0| |n#0@@40| |llen#0@0|)))
 (and (|_module.__default.AbLt#canCall| |n#0@@40| |s#1@@11|) (=> (or (_module.__default.AbLt |n#0@@40| |s#1@@11|) (= |n#0@@40| |s#1@@11|)) (and (and (and (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|) (|_module.__default.AbLt#canCall| |s#1@@11| (_module.__default.AbInc |n#0@@40| |llen#0@0|))) (=> (not (_module.__default.AbLt |s#1@@11| (_module.__default.AbInc |n#0@@40| |llen#0@0|))) (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|))) (=> (or (_module.__default.AbLt |s#1@@11| (_module.__default.AbInc |n#0@@40| |llen#0@0|)) (= |s#1@@11| (_module.__default.AbInc |n#0@@40| |llen#0@0|))) (and (|_module.__default.Elements#canCall| |L#0@0|) (=> (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |L#0@0|) |s#1@@11|))) (forall ((|x#3@@4| T@U) ) (!  (=> (and (= (type |x#3@@4|) BoxType) ($IsBox |x#3@@4| |#$AbInt|)) (and (|_module.__default.AbLt#canCall| |n#0@@40| |x#3@@4|) (=> (or (_module.__default.AbLt |n#0@@40| |x#3@@4|) (= |n#0@@40| |x#3@@4|)) (and (|_module.__default.AbLt#canCall| |x#3@@4| |s#1@@11|) (=> (_module.__default.AbLt |x#3@@4| |s#1@@11|) (|_module.__default.Elements#canCall| |L#0@0|))))))
 :qid |SMNADTLi.363:12|
 :skolemid |1192|
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |L#0@0|) |x#3@@4|))
 :pattern ( (_module.__default.AbLt |x#3@@4| |s#1@@11|))
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#3@@4|))
)))))))))) (let ((|s#1@@12| (_module.__default.SMN_k ($LS ($LS $LZ)) |L#0@0| |n#0@@40| |llen#0@0|)))
 (or (_module.__default.AbLt |n#0@@40| |s#1@@12|) (= |n#0@@40| |s#1@@12|)))) (and (and (let ((|s#1@@13| (_module.__default.SMN_k ($LS ($LS $LZ)) |L#0@0| |n#0@@40| |llen#0@0|)))
 (or (_module.__default.AbLt |s#1@@13| (_module.__default.AbInc |n#0@@40| |llen#0@0|)) (= |s#1@@13| (_module.__default.AbInc |n#0@@40| |llen#0@0|)))) (let ((|s#1@@14| (_module.__default.SMN_k ($LS ($LS $LZ)) |L#0@0| |n#0@@40| |llen#0@0|)))
 (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS ($LS $LZ)) |L#0@0|) |s#1@@14|))))) (and (let ((|s#1@@15| (_module.__default.SMN_k ($LS ($LS $LZ)) |L#0@0| |n#0@@40| |llen#0@0|)))
(forall ((|x#3@@5| T@U) ) (!  (=> (and (and (= (type |x#3@@5|) BoxType) ($IsBox |x#3@@5| |#$AbInt|)) (and (or (_module.__default.AbLt |n#0@@40| |x#3@@5|) (= |n#0@@40| |x#3@@5|)) (_module.__default.AbLt |x#3@@5| |s#1@@15|))) (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |L#0@0|) |x#3@@5|)))
 :qid |SMNADTLi.363:12|
 :skolemid |1194|
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |L#0@0|) |x#3@@5|))
 :pattern ( (_module.__default.AbLt |x#3@@5| |s#1@@15|))
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#3@@5|))
))) (= $Heap@13 $Heap@14)))) (and (! (or %lbl%@44 (forall (($o@@92 T@U) ($f@@82 T@U) ) (! (let ((alpha@@65 (FieldTypeInv0 (type $f@@82))))
 (=> (and (and (= (type $o@@92) refType) (= (type $f@@82) (FieldType alpha@@65))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@92 $f@@82))))
 :qid |SMNADTLi.393:25|
 :skolemid |1217|
 :no-pattern (type $o@@92)
 :no-pattern (type $f@@82)
 :no-pattern (U_2_int $o@@92)
 :no-pattern (U_2_bool $o@@92)
 :no-pattern (U_2_int $f@@82)
 :no-pattern (U_2_bool $f@@82)
))) :lblneg @44) (=> (forall (($o@@93 T@U) ($f@@83 T@U) ) (! (let ((alpha@@66 (FieldTypeInv0 (type $f@@83))))
 (=> (and (and (= (type $o@@93) refType) (= (type $f@@83) (FieldType alpha@@66))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@93 $f@@83))))
 :qid |SMNADTLi.393:25|
 :skolemid |1217|
 :no-pattern (type@@0 $o@@56)
 :no-pattern (type@@0 $f@@46)
 :no-pattern (type $o@@93)
 :no-pattern (type $f@@83)
 :no-pattern (U_2_int $o@@93)
 :no-pattern (U_2_bool $o@@93)
 :no-pattern (U_2_int $f@@83)
 :no-pattern (U_2_bool $f@@83)
)) (=> (and (and (and ($IsGoodHeap $Heap@15) ($IsHeapAnchor $Heap@15)) (forall ((|x#1@@13| T@U) (|a#1| T@U) (|b#1| T@U) ) (!  (=> (and (and (and (= (type |x#1@@13|) BoxType) (= (type |a#1|) BoxType)) (= (type |b#1|) BoxType)) (and (and ($IsBox |x#1@@13| |#$AbInt|) ($IsBox |a#1| |#$AbInt|)) ($IsBox |b#1| |#$AbInt|))) (and (|_module.__default.AbLt#canCall| |a#1| |b#1|) (=> (_module.__default.AbLt |a#1| |b#1|) (and (and (|_module.__default.AbInc#canCall| |x#1@@13| |a#1|) (|_module.__default.AbInc#canCall| |x#1@@13| |b#1|)) (|_module.__default.AbLt#canCall| (_module.__default.AbInc |x#1@@13| |a#1|) (_module.__default.AbInc |x#1@@13| |b#1|))))))
 :qid |SMNADTLi.61:18|
 :skolemid |979|
 :pattern ( (_module.__default.AbInc |x#1@@13| |b#1|) (_module.__default.AbInc |x#1@@13| |a#1|))
))) (and (forall ((|x#1@@14| T@U) (|a#1@@0| T@U) (|b#1@@0| T@U) ) (!  (=> (and (and (and (and (= (type |x#1@@14|) BoxType) (= (type |a#1@@0|) BoxType)) (= (type |b#1@@0|) BoxType)) (and (and ($IsBox |x#1@@14| |#$AbInt|) ($IsBox |a#1@@0| |#$AbInt|)) ($IsBox |b#1@@0| |#$AbInt|))) (_module.__default.AbLt |a#1@@0| |b#1@@0|)) (_module.__default.AbLt (_module.__default.AbInc |x#1@@14| |a#1@@0|) (_module.__default.AbInc |x#1@@14| |b#1@@0|)))
 :qid |SMNADTLi.61:18|
 :skolemid |980|
 :pattern ( (_module.__default.AbInc |x#1@@14| |b#1@@0|) (_module.__default.AbInc |x#1@@14| |a#1@@0|))
)) (= $Heap@14 $Heap@15))) (and (! (or %lbl%@45 (forall (($o@@94 T@U) ($f@@84 T@U) ) (! (let ((alpha@@67 (FieldTypeInv0 (type $f@@84))))
 (=> (and (and (= (type $o@@94) refType) (= (type $f@@84) (FieldType alpha@@67))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@94 $f@@84))))
 :qid |SMNADTLi.394:31|
 :skolemid |1218|
 :no-pattern (type $o@@94)
 :no-pattern (type $f@@84)
 :no-pattern (U_2_int $o@@94)
 :no-pattern (U_2_bool $o@@94)
 :no-pattern (U_2_int $f@@84)
 :no-pattern (U_2_bool $f@@84)
))) :lblneg @45) (=> (forall (($o@@95 T@U) ($f@@85 T@U) ) (! (let ((alpha@@68 (FieldTypeInv0 (type $f@@85))))
 (=> (and (and (= (type $o@@95) refType) (= (type $f@@85) (FieldType alpha@@68))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@95 $f@@85))))
 :qid |SMNADTLi.394:31|
 :skolemid |1218|
 :no-pattern (type@@0 $o@@57)
 :no-pattern (type@@0 $f@@47)
 :no-pattern (type $o@@95)
 :no-pattern (type $f@@85)
 :no-pattern (U_2_int $o@@95)
 :no-pattern (U_2_bool $o@@95)
 :no-pattern (U_2_int $f@@85)
 :no-pattern (U_2_bool $f@@85)
)) (=> (and ($IsGoodHeap $Heap@16) ($IsHeapAnchor $Heap@16)) (=> (and (and (|_module.__default.AbInc#canCall| |n#0@@40| |llen#0@0|) (=> (= |s#1_0@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|)) (and (|_module.__default.AbLt#canCall| |llen#0@0| |len#0@@26|) (=> (_module.__default.AbLt |llen#0@0| |len#0@@26|) (and (|_module.__default.AbInc#canCall| |n#0@@40| |len#0@@26|) (|_module.__default.AbLt#canCall| |s#1_0@0| (_module.__default.AbInc |n#0@@40| |len#0@@26|))))))) (and (=> (and (= |s#1_0@0| (_module.__default.AbInc |n#0@@40| |llen#0@0|)) (_module.__default.AbLt |llen#0@0| |len#0@@26|)) (_module.__default.AbLt |s#1_0@0| (_module.__default.AbInc |n#0@@40| |len#0@@26|))) (= $Heap@15 $Heap@16))) GeneratedUnifiedExit_correct)))))))))))))))))))))))))))))))))))))))
(let ((anon15_Else_correct  (=> (! (and %lbl%+46 true) :lblpos +46) (=> (and (not (|_module.List#Equal| |xs#0@@49| |#_module.List.Nil|)) ($IsAllocBox |len#0@@26| |#$AbInt| $Heap@0)) (=> (and (and (|_module.__default.AbInc1#canCall| |len#0@@26|) (= |##n#9@0| (_module.__default.AbInc1 |len#0@@26|))) (and ($IsAllocBox |##n#9@0| |#$AbInt| $Heap@0) (|_module.__default.AbDiv2#canCall| (_module.__default.AbInc1 |len#0@@26|)))) (=> (and (and (and (and (and (|_module.__default.AbInc1#canCall| |len#0@@26|) (|_module.__default.AbDiv2#canCall| (_module.__default.AbInc1 |len#0@@26|))) (= |half#0@0| (_module.__default.AbDiv2 (_module.__default.AbInc1 |len#0@@26|)))) (and ($Is |L#0@0| (Tclass._module.List |#$AbInt|)) ($IsAlloc |L#0@0| (Tclass._module.List |#$AbInt|) $Heap@0))) (and (and (and ($Is |R#0@0| (Tclass._module.List |#$AbInt|)) ($IsAlloc |R#0@0| (Tclass._module.List |#$AbInt|) $Heap@0)) ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@0)) (and (and ($IsAllocBox |half#0@0| |#$AbInt| $Heap@0) (|_module.__default.AbInc#canCall| |n#0@@40| |half#0@0|)) (and ($IsAlloc |xs#0@@49| (Tclass._module.List |#$AbInt|) $Heap@0) (= |##b#0@0| (_module.__default.AbInc |n#0@@40| |half#0@0|)))))) (and (and (and (and ($IsAllocBox |##b#0@0| |#$AbInt| $Heap@0) (|_module.__default.Split#canCall| |xs#0@@49| (_module.__default.AbInc |n#0@@40| |half#0@0|))) (and (_System.Tuple2.___hMake2_q (_module.__default.Split ($LS $LZ) |xs#0@@49| (_module.__default.AbInc |n#0@@40| |half#0@0|))) (= |let#1#0#0| (_module.__default.Split ($LS $LZ) |xs#0@@49| (_module.__default.AbInc |n#0@@40| |half#0@0|))))) (and (and (|_module.__default.AbInc#canCall| |n#0@@40| |half#0@0|) (|_module.__default.Split#canCall| |xs#0@@49| (_module.__default.AbInc |n#0@@40| |half#0@0|))) ($Is |let#1#0#0| (Tclass._System.Tuple2 (Tclass._module.List |#$AbInt|) (Tclass._module.List |#$AbInt|))))) (and (and (and (_System.Tuple2.___hMake2_q |let#1#0#0|) (_System.Tuple2.___hMake2_q |let#1#0#0|)) (and (= (|#_System._tuple#2._#Make2| ($Box |L#0@0|) ($Box |R#0@0|)) |let#1#0#0|) ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@0))) (and (and ($IsAllocBox |half#0@0| |#$AbInt| $Heap@0) (|_module.__default.AbInc#canCall| |n#0@@40| |half#0@0|)) (and (|_module.__default.AbInc#canCall| |n#0@@40| |half#0@0|) (= |b##0@0| (_module.__default.AbInc |n#0@@40| |half#0@0|))))))) (and (! (or %lbl%@47 (forall (($o@@96 T@U) ($f@@86 T@U) ) (! (let ((alpha@@69 (FieldTypeInv0 (type $f@@86))))
 (=> (and (and (= (type $o@@96) refType) (= (type $f@@86) (FieldType alpha@@69))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@96 $f@@86))))
 :qid |SMNADTLi.373:18|
 :skolemid |1205|
 :no-pattern (type $o@@96)
 :no-pattern (type $f@@86)
 :no-pattern (U_2_int $o@@96)
 :no-pattern (U_2_bool $o@@96)
 :no-pattern (U_2_int $f@@86)
 :no-pattern (U_2_bool $f@@86)
))) :lblneg @47) (=> (forall (($o@@97 T@U) ($f@@87 T@U) ) (! (let ((alpha@@70 (FieldTypeInv0 (type $f@@87))))
 (=> (and (and (= (type $o@@97) refType) (= (type $f@@87) (FieldType alpha@@70))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@97 $f@@87))))
 :qid |SMNADTLi.373:18|
 :skolemid |1205|
 :no-pattern (type@@0 $o@@58)
 :no-pattern (type@@0 $f@@48)
 :no-pattern (type $o@@97)
 :no-pattern (type $f@@87)
 :no-pattern (U_2_int $o@@97)
 :no-pattern (U_2_bool $o@@97)
 :no-pattern (U_2_int $f@@87)
 :no-pattern (U_2_bool $f@@87)
)) (and (! (or %lbl%@48 (_module.__default.NoDuplicates ($LS ($LS $LZ)) |xs#0@@49|)) :lblneg @48) (=> (_module.__default.NoDuplicates ($LS ($LS $LZ)) |xs#0@@49|) (=> (and ($IsGoodHeap $Heap@3) ($IsHeapAnchor $Heap@3)) (=> (and (and (|_module.__default.Split#canCall| |xs#0@@49| |b##0@0|) (let ((|r#1| (_module.__default.Split ($LS $LZ) |xs#0@@49| |b##0@0|)))
 (and (and (and (_System.Tuple2.___hMake2_q |r#1|) (|_module.__default.Elements#canCall| ($Unbox DatatypeTypeType (_System.Tuple2._0 |r#1|)))) (forall ((|x#2@@3| T@U) ) (!  (=> (and (= (type |x#2@@3|) BoxType) ($IsBox |x#2@@3| |#$AbInt|)) (and (|_module.__default.Elements#canCall| |xs#0@@49|) (=> (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#2@@3|)) (|_module.__default.AbLt#canCall| |x#2@@3| |b##0@0|))))
 :qid |SMNADTLi.128:27|
 :skolemid |1038|
 :pattern ( (_module.__default.AbLt |x#2@@3| |b##0@0|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#2@@3|))
))) (=> (|Set#Equal| (_module.__default.Elements ($LS $LZ) ($Unbox DatatypeTypeType (_System.Tuple2._0 |r#1|))) (|lambda#10| |#$AbInt| (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |b##0@0|)) (and (and (and (_System.Tuple2.___hMake2_q |r#1|) (|_module.__default.Elements#canCall| ($Unbox DatatypeTypeType (_System.Tuple2._1 |r#1|)))) (forall ((|x#3@@6| T@U) ) (!  (=> (and (= (type |x#3@@6|) BoxType) ($IsBox |x#3@@6| |#$AbInt|)) (and (|_module.__default.Elements#canCall| |xs#0@@49|) (=> (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#3@@6|)) (|_module.__default.AbLt#canCall| |x#3@@6| |b##0@0|))))
 :qid |SMNADTLi.129:27|
 :skolemid |1039|
 :pattern ( (_module.__default.AbLt |x#3@@6| |b##0@0|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#3@@6|))
))) (=> (|Set#Equal| (_module.__default.Elements ($LS $LZ) ($Unbox DatatypeTypeType (_System.Tuple2._1 |r#1|))) (|lambda#11| |#$AbInt| (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |b##0@0|)) (and (and (_System.Tuple2.___hMake2_q |r#1|) (|_module.__default.NoDuplicates#canCall| ($Unbox DatatypeTypeType (_System.Tuple2._0 |r#1|)))) (=> (_module.__default.NoDuplicates ($LS $LZ) ($Unbox DatatypeTypeType (_System.Tuple2._0 |r#1|))) (and (_System.Tuple2.___hMake2_q |r#1|) (|_module.__default.NoDuplicates#canCall| ($Unbox DatatypeTypeType (_System.Tuple2._1 |r#1|)))))))))))) (let ((|r#1@@0| (_module.__default.Split ($LS ($LS $LZ)) |xs#0@@49| |b##0@0|)))
(|Set#Equal| (_module.__default.Elements ($LS ($LS $LZ)) ($Unbox DatatypeTypeType (_System.Tuple2._0 |r#1@@0|))) (|lambda#10| |#$AbInt| (_module.__default.Elements ($LS ($LS $LZ)) |xs#0@@49|) |b##0@0|)))) (=> (and (and (and (let ((|r#1@@1| (_module.__default.Split ($LS ($LS $LZ)) |xs#0@@49| |b##0@0|)))
(|Set#Equal| (_module.__default.Elements ($LS ($LS $LZ)) ($Unbox DatatypeTypeType (_System.Tuple2._1 |r#1@@1|))) (|lambda#11| |#$AbInt| (_module.__default.Elements ($LS ($LS $LZ)) |xs#0@@49|) |b##0@0|))) (let ((|r#1@@2| (_module.__default.Split ($LS ($LS $LZ)) |xs#0@@49| |b##0@0|)))
(_module.__default.NoDuplicates ($LS ($LS $LZ)) ($Unbox DatatypeTypeType (_System.Tuple2._0 |r#1@@2|))))) (and (let ((|r#1@@3| (_module.__default.Split ($LS ($LS $LZ)) |xs#0@@49| |b##0@0|)))
(_module.__default.NoDuplicates ($LS ($LS $LZ)) ($Unbox DatatypeTypeType (_System.Tuple2._1 |r#1@@3|)))) (= $Heap@0 $Heap@3))) (and (and ($IsAlloc |L#0@0| (Tclass._module.List |#$AbInt|) $Heap@3) (|_module.__default.Length#canCall| |L#0@0|)) (and (|_module.__default.Length#canCall| |L#0@0|) (= |llen#0@0| (_module.__default.Length ($LS $LZ) |L#0@0|))))) (and (! (or %lbl%@49 (forall (($o@@98 T@U) ($f@@88 T@U) ) (! (let ((alpha@@71 (FieldTypeInv0 (type $f@@88))))
 (=> (and (and (= (type $o@@98) refType) (= (type $f@@88) (FieldType alpha@@71))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@98 $f@@88))))
 :qid |SMNADTLi.375:22|
 :skolemid |1206|
 :no-pattern (type $o@@98)
 :no-pattern (type $f@@88)
 :no-pattern (U_2_int $o@@98)
 :no-pattern (U_2_bool $o@@98)
 :no-pattern (U_2_int $f@@88)
 :no-pattern (U_2_bool $f@@88)
))) :lblneg @49) (=> (forall (($o@@99 T@U) ($f@@89 T@U) ) (! (let ((alpha@@72 (FieldTypeInv0 (type $f@@89))))
 (=> (and (and (= (type $o@@99) refType) (= (type $f@@89) (FieldType alpha@@72))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@99 $f@@89))))
 :qid |SMNADTLi.375:22|
 :skolemid |1206|
 :no-pattern (type@@0 $o@@59)
 :no-pattern (type@@0 $f@@49)
 :no-pattern (type $o@@99)
 :no-pattern (type $f@@89)
 :no-pattern (U_2_int $o@@99)
 :no-pattern (U_2_bool $o@@99)
 :no-pattern (U_2_int $f@@89)
 :no-pattern (U_2_bool $f@@89)
)) (and (! (or %lbl%@50 (_module.__default.NoDuplicates ($LS ($LS $LZ)) |L#0@0|)) :lblneg @50) (=> (_module.__default.NoDuplicates ($LS ($LS $LZ)) |L#0@0|) (=> (and ($IsGoodHeap $Heap@4) ($IsHeapAnchor $Heap@4)) (=> (and (and (and (and (and (|_module.__default.Elements#canCall| |L#0@0|) (|_module.__default.AbSetLen#canCall| (_module.__default.Elements ($LS $LZ) |L#0@0|))) (|_module.__default.Length#canCall| |L#0@0|)) (= (_module.__default.AbSetLen (_module.__default.Elements ($LS ($LS $LZ)) |L#0@0|)) (_module.__default.Length ($LS ($LS $LZ)) |L#0@0|))) (and (= $Heap@3 $Heap@4) ($IsAllocBox |n#0@@40| |#$AbInt| $Heap@4))) (and (and (and ($IsAllocBox |half#0@0| |#$AbInt| $Heap@4) (|_module.__default.IntRange#canCall| |n#0@@40| |half#0@0|)) (and (|_module.__default.IntRange#canCall| |n#0@@40| |half#0@0|) (= |bound#0@0| (_module.__default.IntRange |n#0@@40| |half#0@0|)))) (and (and ($IsAlloc |L#0@0| (Tclass._module.List |#$AbInt|) $Heap@4) (|_module.__default.Elements#canCall| |L#0@0|)) (and (|_module.__default.Elements#canCall| |L#0@0|) (= |A##0@0| (_module.__default.Elements ($LS $LZ) |L#0@0|)))))) (and (! (or %lbl%@51 (forall (($o@@100 T@U) ($f@@90 T@U) ) (! (let ((alpha@@73 (FieldTypeInv0 (type $f@@90))))
 (=> (and (and (= (type $o@@100) refType) (= (type $f@@90) (FieldType alpha@@73))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@100 $f@@90))))
 :qid |SMNADTLi.377:16|
 :skolemid |1207|
 :no-pattern (type $o@@100)
 :no-pattern (type $f@@90)
 :no-pattern (U_2_int $o@@100)
 :no-pattern (U_2_bool $o@@100)
 :no-pattern (U_2_int $f@@90)
 :no-pattern (U_2_bool $f@@90)
))) :lblneg @51) (=> (forall (($o@@101 T@U) ($f@@91 T@U) ) (! (let ((alpha@@74 (FieldTypeInv0 (type $f@@91))))
 (=> (and (and (= (type $o@@101) refType) (= (type $f@@91) (FieldType alpha@@74))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@101 $f@@91))))
 :qid |SMNADTLi.377:16|
 :skolemid |1207|
 :no-pattern (type@@0 $o@@60)
 :no-pattern (type@@0 $f@@50)
 :no-pattern (type $o@@101)
 :no-pattern (type $f@@91)
 :no-pattern (U_2_int $o@@101)
 :no-pattern (U_2_bool $o@@101)
 :no-pattern (U_2_int $f@@91)
 :no-pattern (U_2_bool $f@@91)
)) (and (! (or %lbl%@52 (|Set#Subset| |A##0@0| |bound#0@0|)) :lblneg @52) (=> (|Set#Subset| |A##0@0| |bound#0@0|) (=> (and ($IsGoodHeap $Heap@5) ($IsHeapAnchor $Heap@5)) (=> (and (and (and (and (and (|_module.__default.AbSetLen#canCall| |A##0@0|) (|_module.__default.AbSetLen#canCall| |bound#0@0|)) (|_module.__default.AbLt#canCall| (_module.__default.AbSetLen |A##0@0|) (_module.__default.AbSetLen |bound#0@0|))) (=> (not (_module.__default.AbLt (_module.__default.AbSetLen |A##0@0|) (_module.__default.AbSetLen |bound#0@0|))) (and (|_module.__default.AbSetLen#canCall| |A##0@0|) (|_module.__default.AbSetLen#canCall| |bound#0@0|)))) (or (_module.__default.AbLt (_module.__default.AbSetLen |A##0@0|) (_module.__default.AbSetLen |bound#0@0|)) (= (_module.__default.AbSetLen |A##0@0|) (_module.__default.AbSetLen |bound#0@0|)))) (and (= $Heap@4 $Heap@5) (= |a##0@0| (LitInt 1)))) (and (! (or %lbl%@53 (forall (($o@@102 T@U) ($f@@92 T@U) ) (! (let ((alpha@@75 (FieldTypeInv0 (type $f@@92))))
 (=> (and (and (= (type $o@@102) refType) (= (type $f@@92) (FieldType alpha@@75))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@102 $f@@92))))
 :qid |SMNADTLi.380:18|
 :skolemid |1208|
 :no-pattern (type $o@@102)
 :no-pattern (type $f@@92)
 :no-pattern (U_2_int $o@@102)
 :no-pattern (U_2_bool $o@@102)
 :no-pattern (U_2_int $f@@92)
 :no-pattern (U_2_bool $f@@92)
))) :lblneg @53) (=> (forall (($o@@103 T@U) ($f@@93 T@U) ) (! (let ((alpha@@76 (FieldTypeInv0 (type $f@@93))))
 (=> (and (and (= (type $o@@103) refType) (= (type $f@@93) (FieldType alpha@@76))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@103 $f@@93))))
 :qid |SMNADTLi.380:18|
 :skolemid |1208|
 :no-pattern (type@@0 $o@@61)
 :no-pattern (type@@0 $f@@51)
 :no-pattern (type $o@@103)
 :no-pattern (type $f@@93)
 :no-pattern (U_2_int $o@@103)
 :no-pattern (U_2_bool $o@@103)
 :no-pattern (U_2_int $f@@93)
 :no-pattern (U_2_bool $f@@93)
)) (=> (and (and (and ($IsGoodHeap $Heap@6) ($IsHeapAnchor $Heap@6)) (and (|_module.__default.int2adt#canCall| |a##0@0|) (|_module.__default.AbPos#canCall| (_module.__default.int2adt |a##0@0|)))) (and (and (|_module.__default.AbPos#canCall| (_module.__default.int2adt |a##0@0|)) (and (_module.__default.AbPos (_module.__default.int2adt |a##0@0|)) (not (_module.__default.AbIsZero (_module.__default.int2adt |a##0@0|))))) (= $Heap@5 $Heap@6))) (and (! (or %lbl%@54 (forall (($o@@104 T@U) ($f@@94 T@U) ) (! (let ((alpha@@77 (FieldTypeInv0 (type $f@@94))))
 (=> (and (and (= (type $o@@104) refType) (= (type $f@@94) (FieldType alpha@@77))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@104 $f@@94))))
 :qid |SMNADTLi.381:19|
 :skolemid |1209|
 :no-pattern (type $o@@104)
 :no-pattern (type $f@@94)
 :no-pattern (U_2_int $o@@104)
 :no-pattern (U_2_bool $o@@104)
 :no-pattern (U_2_int $f@@94)
 :no-pattern (U_2_bool $f@@94)
))) :lblneg @54) (=> (forall (($o@@105 T@U) ($f@@95 T@U) ) (! (let ((alpha@@78 (FieldTypeInv0 (type $f@@95))))
 (=> (and (and (= (type $o@@105) refType) (= (type $f@@95) (FieldType alpha@@78))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@105 $f@@95))))
 :qid |SMNADTLi.381:19|
 :skolemid |1209|
 :no-pattern (type@@0 $o@@62)
 :no-pattern (type@@0 $f@@52)
 :no-pattern (type $o@@105)
 :no-pattern (type $f@@95)
 :no-pattern (U_2_int $o@@105)
 :no-pattern (U_2_bool $o@@105)
 :no-pattern (U_2_int $f@@95)
 :no-pattern (U_2_bool $f@@95)
)) (=> (and (and (and ($IsGoodHeap $Heap@7) ($IsHeapAnchor $Heap@7)) (forall ((|x#1@@15| T@U) ) (!  (=> (and (= (type |x#1@@15|) BoxType) ($IsBox |x#1@@15| |#$AbInt|)) (and (and (|_module.__default.AbInc1#canCall| |x#1@@15|) (and (|_module.__default.int2adt#canCall| (LitInt 1)) (|_module.__default.AbInc#canCall| |x#1@@15| (_module.__default.int2adt (LitInt 1))))) (=> (= (_module.__default.AbInc1 |x#1@@15|) (_module.__default.AbInc |x#1@@15| (_module.__default.int2adt (LitInt 1)))) (and (and (|_module.__default.int2adt#canCall| (LitInt 1)) (|_module.__default.AbInc#canCall| |x#1@@15| (_module.__default.int2adt (LitInt 1)))) (and (|_module.__default.int2adt#canCall| (LitInt 1)) (|_module.__default.AbInc#canCall| (_module.__default.int2adt (LitInt 1)) |x#1@@15|))))))
 :qid |SMNADTLi.46:18|
 :skolemid |964|
 :pattern ( (_module.__default.AbInc (_module.__default.int2adt 1) |x#1@@15|))
 :pattern ( (_module.__default.AbInc |x#1@@15| (_module.__default.int2adt 1)))
 :pattern ( (_module.__default.AbInc1 |x#1@@15|))
))) (and (forall ((|x#1@@16| T@U) ) (!  (=> (and (= (type |x#1@@16|) BoxType) ($IsBox |x#1@@16| |#$AbInt|)) (and (= (_module.__default.AbInc1 |x#1@@16|) (_module.__default.AbInc |x#1@@16| (_module.__default.int2adt (LitInt 1)))) (= (_module.__default.AbInc |x#1@@16| (_module.__default.int2adt (LitInt 1))) (_module.__default.AbInc (_module.__default.int2adt (LitInt 1)) |x#1@@16|))))
 :qid |SMNADTLi.46:18|
 :skolemid |965|
 :pattern ( (_module.__default.AbInc (_module.__default.int2adt 1) |x#1@@16|))
 :pattern ( (_module.__default.AbInc |x#1@@16| (_module.__default.int2adt 1)))
 :pattern ( (_module.__default.AbInc1 |x#1@@16|))
)) (= $Heap@6 $Heap@7))) (and (! (or %lbl%@55 (forall (($o@@106 T@U) ($f@@96 T@U) ) (! (let ((alpha@@79 (FieldTypeInv0 (type $f@@96))))
 (=> (and (and (= (type $o@@106) refType) (= (type $f@@96) (FieldType alpha@@79))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@106 $f@@96))))
 :qid |SMNADTLi.381:38|
 :skolemid |1210|
 :no-pattern (type $o@@106)
 :no-pattern (type $f@@96)
 :no-pattern (U_2_int $o@@106)
 :no-pattern (U_2_bool $o@@106)
 :no-pattern (U_2_int $f@@96)
 :no-pattern (U_2_bool $f@@96)
))) :lblneg @55) (=> (forall (($o@@107 T@U) ($f@@97 T@U) ) (! (let ((alpha@@80 (FieldTypeInv0 (type $f@@97))))
 (=> (and (and (= (type $o@@107) refType) (= (type $f@@97) (FieldType alpha@@80))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@107 $f@@97))))
 :qid |SMNADTLi.381:38|
 :skolemid |1210|
 :no-pattern (type@@0 $o@@63)
 :no-pattern (type@@0 $f@@53)
 :no-pattern (type $o@@107)
 :no-pattern (type $f@@97)
 :no-pattern (U_2_int $o@@107)
 :no-pattern (U_2_bool $o@@107)
 :no-pattern (U_2_int $f@@97)
 :no-pattern (U_2_bool $f@@97)
)) (=> (and (and (and ($IsGoodHeap $Heap@8) ($IsHeapAnchor $Heap@8)) (forall ((|x#1@@17| T@U) ) (!  (=> (and (= (type |x#1@@17|) BoxType) ($IsBox |x#1@@17| |#$AbInt|)) (and (and (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbInc#canCall| |x#1@@17| (_module.__default.int2adt (LitInt 0)))) (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbInc#canCall| (_module.__default.int2adt (LitInt 0)) |x#1@@17|))) (=> (= (_module.__default.AbInc |x#1@@17| (_module.__default.int2adt (LitInt 0))) (_module.__default.AbInc (_module.__default.int2adt (LitInt 0)) |x#1@@17|)) (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbInc#canCall| (_module.__default.int2adt (LitInt 0)) |x#1@@17|)))))
 :qid |SMNADTLi.48:18|
 :skolemid |967|
 :pattern ( (_module.__default.AbInc (_module.__default.int2adt 0) |x#1@@17|))
 :pattern ( (_module.__default.AbInc |x#1@@17| (_module.__default.int2adt 0)))
))) (and (forall ((|x#1@@18| T@U) ) (!  (=> (and (= (type |x#1@@18|) BoxType) ($IsBox |x#1@@18| |#$AbInt|)) (and (= (_module.__default.AbInc |x#1@@18| (_module.__default.int2adt (LitInt 0))) (_module.__default.AbInc (_module.__default.int2adt (LitInt 0)) |x#1@@18|)) (= (_module.__default.AbInc (_module.__default.int2adt (LitInt 0)) |x#1@@18|) |x#1@@18|)))
 :qid |SMNADTLi.48:18|
 :skolemid |968|
 :pattern ( (_module.__default.AbInc (_module.__default.int2adt 0) |x#1@@18|))
 :pattern ( (_module.__default.AbInc |x#1@@18| (_module.__default.int2adt 0)))
)) (= $Heap@7 $Heap@8))) (and (! (or %lbl%@56 (forall (($o@@108 T@U) ($f@@98 T@U) ) (! (let ((alpha@@81 (FieldTypeInv0 (type $f@@98))))
 (=> (and (and (= (type $o@@108) refType) (= (type $f@@98) (FieldType alpha@@81))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@108 $f@@98))))
 :qid |SMNADTLi.382:25|
 :skolemid |1211|
 :no-pattern (type $o@@108)
 :no-pattern (type $f@@98)
 :no-pattern (U_2_int $o@@108)
 :no-pattern (U_2_bool $o@@108)
 :no-pattern (U_2_int $f@@98)
 :no-pattern (U_2_bool $f@@98)
))) :lblneg @56) (=> (forall (($o@@109 T@U) ($f@@99 T@U) ) (! (let ((alpha@@82 (FieldTypeInv0 (type $f@@99))))
 (=> (and (and (= (type $o@@109) refType) (= (type $f@@99) (FieldType alpha@@82))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@109 $f@@99))))
 :qid |SMNADTLi.382:25|
 :skolemid |1211|
 :no-pattern (type@@0 $o@@64)
 :no-pattern (type@@0 $f@@54)
 :no-pattern (type $o@@109)
 :no-pattern (type $f@@99)
 :no-pattern (U_2_int $o@@109)
 :no-pattern (U_2_bool $o@@109)
 :no-pattern (U_2_int $f@@99)
 :no-pattern (U_2_bool $f@@99)
)) (=> (and (and (and ($IsGoodHeap $Heap@9) ($IsHeapAnchor $Heap@9)) (forall ((|x#1@@19| T@U) (|y#1@@3| T@U) ) (!  (=> (and (and (= (type |x#1@@19|) BoxType) (= (type |y#1@@3|) BoxType)) (and ($IsBox |x#1@@19| |#$AbInt|) ($IsBox |y#1@@3| |#$AbInt|))) (and (|_module.__default.AbPos#canCall| |y#1@@3|) (=> (_module.__default.AbPos |y#1@@3|) (and (|_module.__default.AbInc#canCall| |x#1@@19| |y#1@@3|) (|_module.__default.AbLt#canCall| |x#1@@19| (_module.__default.AbInc |x#1@@19| |y#1@@3|))))))
 :qid |SMNADTLi.77:18|
 :skolemid |1001|
 :pattern ( (_module.__default.AbInc |x#1@@19| |y#1@@3|))
))) (and (and (forall ((|x#1@@20| T@U) (|y#1@@4| T@U) ) (!  (=> (and (and (and (= (type |x#1@@20|) BoxType) (= (type |y#1@@4|) BoxType)) (and ($IsBox |x#1@@20| |#$AbInt|) ($IsBox |y#1@@4| |#$AbInt|))) (_module.__default.AbPos |y#1@@4|)) (_module.__default.AbLt |x#1@@20| (_module.__default.AbInc |x#1@@20| |y#1@@4|)))
 :qid |SMNADTLi.77:18|
 :skolemid |1002|
 :pattern ( (_module.__default.AbInc |x#1@@20| |y#1@@4|))
)) (forall ((|x#3@@7| T@U) (|y#3| T@U) ) (!  (=> (and (and (= (type |x#3@@7|) BoxType) (= (type |y#3|) BoxType)) (and ($IsBox |x#3@@7| |#$AbInt|) ($IsBox |y#3| |#$AbInt|))) (and (|_module.__default.AbPos#canCall| |y#3|) (=> (_module.__default.AbPos |y#3|) (and (|_module.__default.AbInc#canCall| |y#3| |x#3@@7|) (|_module.__default.AbLt#canCall| |x#3@@7| (_module.__default.AbInc |y#3| |x#3@@7|))))))
 :qid |SMNADTLi.78:18|
 :skolemid |1003|
 :pattern ( (_module.__default.AbInc |y#3| |x#3@@7|))
))) (and (forall ((|x#3@@8| T@U) (|y#3@@0| T@U) ) (!  (=> (and (and (and (= (type |x#3@@8|) BoxType) (= (type |y#3@@0|) BoxType)) (and ($IsBox |x#3@@8| |#$AbInt|) ($IsBox |y#3@@0| |#$AbInt|))) (_module.__default.AbPos |y#3@@0|)) (_module.__default.AbLt |x#3@@8| (_module.__default.AbInc |y#3@@0| |x#3@@8|)))
 :qid |SMNADTLi.78:18|
 :skolemid |1004|
 :pattern ( (_module.__default.AbInc |y#3@@0| |x#3@@8|))
)) (= $Heap@8 $Heap@9)))) (and (! (or %lbl%@57 (forall (($o@@110 T@U) ($f@@100 T@U) ) (! (let ((alpha@@83 (FieldTypeInv0 (type $f@@100))))
 (=> (and (and (= (type $o@@110) refType) (= (type $f@@100) (FieldType alpha@@83))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@110 $f@@100))))
 :qid |SMNADTLi.383:25|
 :skolemid |1212|
 :no-pattern (type $o@@110)
 :no-pattern (type $f@@100)
 :no-pattern (U_2_int $o@@110)
 :no-pattern (U_2_bool $o@@110)
 :no-pattern (U_2_int $f@@100)
 :no-pattern (U_2_bool $f@@100)
))) :lblneg @57) (=> (forall (($o@@111 T@U) ($f@@101 T@U) ) (! (let ((alpha@@84 (FieldTypeInv0 (type $f@@101))))
 (=> (and (and (= (type $o@@111) refType) (= (type $f@@101) (FieldType alpha@@84))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@111 $f@@101))))
 :qid |SMNADTLi.383:25|
 :skolemid |1212|
 :no-pattern (type@@0 $o@@65)
 :no-pattern (type@@0 $f@@55)
 :no-pattern (type $o@@111)
 :no-pattern (type $f@@101)
 :no-pattern (U_2_int $o@@111)
 :no-pattern (U_2_bool $o@@111)
 :no-pattern (U_2_int $f@@101)
 :no-pattern (U_2_bool $f@@101)
)) (=> (and (and (and (and ($IsGoodHeap $Heap@10) ($IsHeapAnchor $Heap@10)) (forall ((|x#1@@21| T@U) (|y#1@@5| T@U) (|z#1@@1| T@U) ) (!  (=> (and (and (and (= (type |x#1@@21|) BoxType) (= (type |y#1@@5|) BoxType)) (= (type |z#1@@1|) BoxType)) (and (and ($IsBox |x#1@@21| |#$AbInt|) ($IsBox |y#1@@5| |#$AbInt|)) ($IsBox |z#1@@1| |#$AbInt|))) (and (|_module.__default.AbLt#canCall| |x#1@@21| |y#1@@5|) (=> (_module.__default.AbLt |x#1@@21| |y#1@@5|) (and (|_module.__default.AbLt#canCall| |y#1@@5| |z#1@@1|) (=> (_module.__default.AbLt |y#1@@5| |z#1@@1|) (|_module.__default.AbLt#canCall| |x#1@@21| |z#1@@1|))))))
 :qid |SMNADTLi.63:18|
 :skolemid |982|
 :pattern ( (_module.__default.AbLt |x#1@@21| |z#1@@1|) (_module.__default.AbLt |y#1@@5| |z#1@@1|))
 :pattern ( (_module.__default.AbLt |y#1@@5| |z#1@@1|) (_module.__default.AbLt |x#1@@21| |y#1@@5|))
))) (and (forall ((|x#1@@22| T@U) (|y#1@@6| T@U) (|z#1@@2| T@U) ) (!  (=> (and (and (and (and (= (type |x#1@@22|) BoxType) (= (type |y#1@@6|) BoxType)) (= (type |z#1@@2|) BoxType)) (and (and ($IsBox |x#1@@22| |#$AbInt|) ($IsBox |y#1@@6| |#$AbInt|)) ($IsBox |z#1@@2| |#$AbInt|))) (and (_module.__default.AbLt |x#1@@22| |y#1@@6|) (_module.__default.AbLt |y#1@@6| |z#1@@2|))) (_module.__default.AbLt |x#1@@22| |z#1@@2|))
 :qid |SMNADTLi.63:18|
 :skolemid |983|
 :pattern ( (_module.__default.AbLt |x#1@@22| |z#1@@2|) (_module.__default.AbLt |y#1@@6| |z#1@@2|))
 :pattern ( (_module.__default.AbLt |y#1@@6| |z#1@@2|) (_module.__default.AbLt |x#1@@22| |y#1@@6|))
)) (= $Heap@9 $Heap@10))) (and (and ($IsAllocBox |llen#0@0| |#$AbInt| $Heap@10) ($IsAllocBox |half#0@0| |#$AbInt| $Heap@10)) (and (|_module.__default.AbLt#canCall| |llen#0@0| |half#0@0|) (|_module.__default.AbLt#canCall| |llen#0@0| |half#0@0|)))) (and anon16_Then_correct anon16_Else_correct)))))))))))))))))))))))))))))))))))))))))
(let ((anon15_Then_correct  (=> (! (and %lbl%+58 true) :lblpos +58) (=> (|_module.List#Equal| |xs#0@@49| |#_module.List.Nil|) (and (! (or %lbl%@59 (forall (($o@@112 T@U) ($f@@102 T@U) ) (! (let ((alpha@@85 (FieldTypeInv0 (type $f@@102))))
 (=> (and (and (= (type $o@@112) refType) (= (type $f@@102) (FieldType alpha@@85))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@112 $f@@102))))
 :qid |SMNADTLi.367:20|
 :skolemid |1203|
 :no-pattern (type $o@@112)
 :no-pattern (type $f@@102)
 :no-pattern (U_2_int $o@@112)
 :no-pattern (U_2_bool $o@@112)
 :no-pattern (U_2_int $f@@102)
 :no-pattern (U_2_bool $f@@102)
))) :lblneg @59) (=> (forall (($o@@113 T@U) ($f@@103 T@U) ) (! (let ((alpha@@86 (FieldTypeInv0 (type $f@@103))))
 (=> (and (and (= (type $o@@113) refType) (= (type $f@@103) (FieldType alpha@@86))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@113 $f@@103))))
 :qid |SMNADTLi.367:20|
 :skolemid |1203|
 :no-pattern (type@@0 $o@@66)
 :no-pattern (type@@0 $f@@56)
 :no-pattern (type $o@@113)
 :no-pattern (type $f@@103)
 :no-pattern (U_2_int $o@@113)
 :no-pattern (U_2_bool $o@@113)
 :no-pattern (U_2_int $f@@103)
 :no-pattern (U_2_bool $f@@103)
)) (=> (and (and (and ($IsGoodHeap $Heap@1) ($IsHeapAnchor $Heap@1)) (forall ((|x#1@@23| T@U) ) (!  (=> (and (= (type |x#1@@23|) BoxType) ($IsBox |x#1@@23| |#$AbInt|)) (and (and (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbInc#canCall| |x#1@@23| (_module.__default.int2adt (LitInt 0)))) (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbInc#canCall| (_module.__default.int2adt (LitInt 0)) |x#1@@23|))) (=> (= (_module.__default.AbInc |x#1@@23| (_module.__default.int2adt (LitInt 0))) (_module.__default.AbInc (_module.__default.int2adt (LitInt 0)) |x#1@@23|)) (and (|_module.__default.int2adt#canCall| (LitInt 0)) (|_module.__default.AbInc#canCall| (_module.__default.int2adt (LitInt 0)) |x#1@@23|)))))
 :qid |SMNADTLi.48:18|
 :skolemid |967|
 :pattern ( (_module.__default.AbInc (_module.__default.int2adt 0) |x#1@@23|))
 :pattern ( (_module.__default.AbInc |x#1@@23| (_module.__default.int2adt 0)))
))) (and (forall ((|x#1@@24| T@U) ) (!  (=> (and (= (type |x#1@@24|) BoxType) ($IsBox |x#1@@24| |#$AbInt|)) (and (= (_module.__default.AbInc |x#1@@24| (_module.__default.int2adt (LitInt 0))) (_module.__default.AbInc (_module.__default.int2adt (LitInt 0)) |x#1@@24|)) (= (_module.__default.AbInc (_module.__default.int2adt (LitInt 0)) |x#1@@24|) |x#1@@24|)))
 :qid |SMNADTLi.48:18|
 :skolemid |968|
 :pattern ( (_module.__default.AbInc (_module.__default.int2adt 0) |x#1@@24|))
 :pattern ( (_module.__default.AbInc |x#1@@24| (_module.__default.int2adt 0)))
)) (= $Heap@0 $Heap@1))) (and (! (or %lbl%@60 (forall (($o@@114 T@U) ($f@@104 T@U) ) (! (let ((alpha@@87 (FieldTypeInv0 (type $f@@104))))
 (=> (and (and (= (type $o@@114) refType) (= (type $f@@104) (FieldType alpha@@87))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@114 $f@@104))))
 :qid |SMNADTLi.368:19|
 :skolemid |1204|
 :no-pattern (type $o@@114)
 :no-pattern (type $f@@104)
 :no-pattern (U_2_int $o@@114)
 :no-pattern (U_2_bool $o@@114)
 :no-pattern (U_2_int $f@@104)
 :no-pattern (U_2_bool $f@@104)
))) :lblneg @60) (=> (forall (($o@@115 T@U) ($f@@105 T@U) ) (! (let ((alpha@@88 (FieldTypeInv0 (type $f@@105))))
 (=> (and (and (= (type $o@@115) refType) (= (type $f@@105) (FieldType alpha@@88))) false) (U_2_bool (MapType5Select $_Frame@0 $o@@115 $f@@105))))
 :qid |SMNADTLi.368:19|
 :skolemid |1204|
 :no-pattern (type@@0 $o@@67)
 :no-pattern (type@@0 $f@@57)
 :no-pattern (type $o@@115)
 :no-pattern (type $f@@105)
 :no-pattern (U_2_int $o@@115)
 :no-pattern (U_2_bool $o@@115)
 :no-pattern (U_2_int $f@@105)
 :no-pattern (U_2_bool $f@@105)
)) (=> (and (and (and ($IsGoodHeap $Heap@2) ($IsHeapAnchor $Heap@2)) (forall ((|x#1@@25| T@U) (|y#1@@7| T@U) ) (!  (=> (and (and (= (type |x#1@@25|) BoxType) (= (type |y#1@@7|) BoxType)) (and ($IsBox |x#1@@25| |#$AbInt|) ($IsBox |y#1@@7| |#$AbInt|))) (and (|_module.__default.AbLt#canCall| |x#1@@25| |y#1@@7|) (|_module.__default.AbLt#canCall| |y#1@@7| |x#1@@25|)))
 :qid |SMNADTLi.52:18|
 :skolemid |970|
 :pattern ( (_module.__default.AbLt |y#1@@7| |x#1@@25|))
 :pattern ( (_module.__default.AbLt |x#1@@25| |y#1@@7|))
))) (and (forall ((|x#1@@26| T@U) (|y#1@@8| T@U) ) (!  (=> (and (and (= (type |x#1@@26|) BoxType) (= (type |y#1@@8|) BoxType)) (and ($IsBox |x#1@@26| |#$AbInt|) ($IsBox |y#1@@8| |#$AbInt|))) (and (=> (_module.__default.AbLt |x#1@@26| |y#1@@8|) (not (or (_module.__default.AbLt |y#1@@8| |x#1@@26|) (= |x#1@@26| |y#1@@8|)))) (=> (not (or (_module.__default.AbLt |y#1@@8| |x#1@@26|) (= |x#1@@26| |y#1@@8|))) (_module.__default.AbLt |x#1@@26| |y#1@@8|))))
 :qid |SMNADTLi.52:18|
 :skolemid |971|
 :pattern ( (_module.__default.AbLt |y#1@@8| |x#1@@26|))
 :pattern ( (_module.__default.AbLt |x#1@@26| |y#1@@8|))
)) (= $Heap@1 $Heap@2))) GeneratedUnifiedExit_correct))))))))))
(let ((anon0_correct  (=> (! (and %lbl%+61 true) :lblpos +61) (=> (and (= $_Frame@0 (|lambda#40| null $Heap alloc false)) (|$IsA#_module.List| |xs#0@@49|)) (=> (and (and (and ($IsGoodHeap $Heap@0) ($IsHeapAnchor $Heap@0)) (= $Heap $Heap@0)) (and (forall ((|$ih#xs0#0| T@U) ) (!  (=> (= (type |$ih#xs0#0|) DatatypeTypeType) (=> (and (and ($Is |$ih#xs0#0| (Tclass._module.List |#$AbInt|)) (and (and (_module.__default.NoDuplicates ($LS $LZ) |$ih#xs0#0|) (forall ((|x#4@@0| T@U) ) (!  (=> (and (and (= (type |x#4@@0|) BoxType) ($IsBox |x#4@@0| |#$AbInt|)) (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |$ih#xs0#0|) |x#4@@0|))) (or (_module.__default.AbLt |n#0@@40| |x#4@@0|) (= |n#0@@40| |x#4@@0|)))
 :qid |SMNADTLi.357:19|
 :skolemid |1200|
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#4@@0|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |$ih#xs0#0|) |x#4@@0|))
))) (= |len#0@@26| (_module.__default.Length ($LS $LZ) |$ih#xs0#0|)))) (< (DtRank (_module.__default.adt2dt |len#0@@26|)) (DtRank (_module.__default.adt2dt |len#0@@26|)))) (let ((|s#2| (_module.__default.SMN_k ($LS $LZ) |$ih#xs0#0| |n#0@@40| |len#0@@26|)))
 (and (and (and (or (_module.__default.AbLt |n#0@@40| |s#2|) (= |n#0@@40| |s#2|)) (or (_module.__default.AbLt |s#2| (_module.__default.AbInc |n#0@@40| |len#0@@26|)) (= |s#2| (_module.__default.AbInc |n#0@@40| |len#0@@26|)))) (not (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |$ih#xs0#0|) |s#2|)))) (forall ((|x#5@@0| T@U) ) (!  (=> (and (and (= (type |x#5@@0|) BoxType) ($IsBox |x#5@@0| |#$AbInt|)) (and (or (_module.__default.AbLt |n#0@@40| |x#5@@0|) (= |n#0@@40| |x#5@@0|)) (_module.__default.AbLt |x#5@@0| |s#2|))) (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |$ih#xs0#0|) |x#5@@0|)))
 :qid |SMNADTLi.363:12|
 :skolemid |1201|
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |$ih#xs0#0|) |x#5@@0|))
 :pattern ( (_module.__default.AbLt |x#5@@0| |s#2|))
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#5@@0|))
))))))
 :qid |SMNADTLi.355:20|
 :skolemid |1202|
 :no-pattern (type |$ih#xs0#0|)
 :no-pattern (U_2_int |$ih#xs0#0|)
 :no-pattern (U_2_bool |$ih#xs0#0|)
)) (|$IsA#_module.List| |xs#0@@49|))) (and anon15_Then_correct anon15_Else_correct))))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+62 true) :lblpos +62) (=> (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (=> (and (and (and ($Is |xs#0@@49| (Tclass._module.List |#$AbInt|)) ($IsAlloc |xs#0@@49| (Tclass._module.List |#$AbInt|) $Heap)) (|$IsA#_module.List| |xs#0@@49|)) (and ($IsBox |n#0@@40| |#$AbInt|) ($IsAllocBox |n#0@@40| |#$AbInt| $Heap))) (=> (and (and (and (and ($IsBox |len#0@@26| |#$AbInt|) ($IsAllocBox |len#0@@26| |#$AbInt| $Heap)) (and ($IsBox |half#0@@3| |#$AbInt|) ($IsAllocBox |half#0@@3| |#$AbInt| $Heap))) (and (and ($IsBox |llen#0@@5| |#$AbInt|) ($IsAllocBox |llen#0@@5| |#$AbInt| $Heap)) (and ($Is |bound#0| (TSet |#$AbInt|)) ($IsAlloc |bound#0| (TSet |#$AbInt|) $Heap)))) (and (and (and ($IsBox |s#1_0| |#$AbInt|) ($IsAllocBox |s#1_0| |#$AbInt| $Heap)) (and ($IsBox |s#3| |#$AbInt|) ($IsAllocBox |s#3| |#$AbInt| $Heap))) (and (and (= 49 $FunctionContextHeight) (_module.__default.NoDuplicates ($LS ($LS $LZ)) |xs#0@@49|)) (and (forall ((|x#1@@27| T@U) ) (!  (=> (and (and (= (type |x#1@@27|) BoxType) ($IsBox |x#1@@27| |#$AbInt|)) (U_2_bool (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#1@@27|))) (or (_module.__default.AbLt |n#0@@40| |x#1@@27|) (= |n#0@@40| |x#1@@27|)))
 :qid |SMNADTLi.357:19|
 :skolemid |1196|
 :pattern ( (_module.__default.AbLt |n#0@@40| |x#1@@27|))
 :pattern ( (MapType0Select (_module.__default.Elements ($LS $LZ) |xs#0@@49|) |x#1@@27|))
)) (= |len#0@@26| (_module.__default.Length ($LS ($LS $LZ)) |xs#0@@49|)))))) anon0_correct))))))
PreconditionGeneratedEntry_correct)))))))))))))))))
))
(check-sat)
(pop 1)
; Valid
