(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.CASE_SPLIT 3)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
(set-option :model.compact false)
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
(declare-fun Tagclass._System.___hFunc3 () T@U)
(declare-fun Tagclass._System.___hPartialFunc3 () T@U)
(declare-fun Tagclass._System.___hTotalFunc3 () T@U)
(declare-fun DtCtorIdType () T@T)
(declare-fun |##_System._tuple#0._#Make0| () T@U)
(declare-fun Tagclass._System.Tuple0 () T@U)
(declare-fun class._System.Tuple0 () T@U)
(declare-fun Tagclass._System.___hFunc5 () T@U)
(declare-fun Tagclass._System.___hPartialFunc5 () T@U)
(declare-fun Tagclass._System.___hTotalFunc5 () T@U)
(declare-fun |##_System._tuple#2._#Make2| () T@U)
(declare-fun Tagclass._System.Tuple2 () T@U)
(declare-fun class._System.Tuple2 () T@U)
(declare-fun |##_module.Option.None| () T@U)
(declare-fun Tagclass._module.Option () T@U)
(declare-fun |##_module.Option.Some| () T@U)
(declare-fun class._module.Option () T@U)
(declare-fun |##_module.Node.Node| () T@U)
(declare-fun Tagclass._module.Node () T@U)
(declare-fun class._module.Node () T@U)
(declare-fun |##_module.DList.DList| () T@U)
(declare-fun Tagclass._module.DList () T@U)
(declare-fun class._module.DList () T@U)
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
(declare-fun DatatypeCtorId (T@U) T@U)
(declare-fun |#_System._tuple#0._#Make0| () T@U)
(declare-fun _System.Tuple0.___hMake0_q (T@U) Bool)
(declare-fun Tclass._System.Tuple0 () T@U)
(declare-fun |$IsA#_System.Tuple0| (T@U) Bool)
(declare-fun |_System.Tuple0#Equal| (T@U T@U) Bool)
(declare-fun Tclass._System.___hFunc5 (T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc5_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc5_1 (T@U) T@U)
(declare-fun Tclass._System.___hFunc5_2 (T@U) T@U)
(declare-fun Tclass._System.___hFunc5_3 (T@U) T@U)
(declare-fun Tclass._System.___hFunc5_4 (T@U) T@U)
(declare-fun Tclass._System.___hFunc5_5 (T@U) T@U)
(declare-fun MapType5Type (T@T T@T T@T T@T T@T T@T T@T) T@T)
(declare-fun MapType5TypeInv0 (T@T) T@T)
(declare-fun MapType5TypeInv1 (T@T) T@T)
(declare-fun MapType5TypeInv2 (T@T) T@T)
(declare-fun MapType5TypeInv3 (T@T) T@T)
(declare-fun MapType5TypeInv4 (T@T) T@T)
(declare-fun MapType5TypeInv5 (T@T) T@T)
(declare-fun MapType5TypeInv6 (T@T) T@T)
(declare-fun MapType5Select (T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun MapType5Store (T@U T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Apply5 (T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Handle5 (T@U T@U T@U) T@U)
(declare-fun Requires5 (T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads5 (T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc5 (T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc5_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc5_1 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc5_2 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc5_3 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc5_4 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc5_5 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc5 (T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc5_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc5_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc5_2 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc5_3 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc5_4 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc5_5 (T@U) T@U)
(declare-fun |#_System._tuple#2._#Make2| (T@U T@U) T@U)
(declare-fun _System.Tuple2.___hMake2_q (T@U) Bool)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
(declare-fun Tclass._System.Tuple2_0 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_1 (T@U) T@U)
(declare-fun |$IsA#_System.Tuple2| (T@U) Bool)
(declare-fun |_System.Tuple2#Equal| (T@U T@U) Bool)
(declare-fun |#_module.Option.None| () T@U)
(declare-fun _module.Option.None_q (T@U) Bool)
(declare-fun Tclass._module.Option (T@U) T@U)
(declare-fun Tclass._module.Option_0 (T@U) T@U)
(declare-fun |#_module.Option.Some| (T@U) T@U)
(declare-fun _module.Option.Some_q (T@U) Bool)
(declare-fun _module.Option.value (T@U) T@U)
(declare-fun |$IsA#_module.Option| (T@U) Bool)
(declare-fun |_module.Option#Equal| (T@U T@U) Bool)
(declare-fun |#_module.Node.Node| (T@U Int Int) T@U)
(declare-fun _module.Node.Node_q (T@U) Bool)
(declare-fun Tclass._module.Node (T@U) T@U)
(declare-fun Tclass._module.Node_0 (T@U) T@U)
(declare-fun _module.Node.data (T@U) T@U)
(declare-fun _module.Node.next (T@U) Int)
(declare-fun _module.Node.prev (T@U) Int)
(declare-fun |$IsA#_module.Node| (T@U) Bool)
(declare-fun |_module.Node#Equal| (T@U T@U) Bool)
(declare-fun |#_module.DList.DList| (T@U Int T@U T@U T@U) T@U)
(declare-fun _module.DList.DList_q (T@U) Bool)
(declare-fun Tclass._module.DList (T@U) T@U)
(declare-fun Tclass._module.DList_0 (T@U) T@U)
(declare-fun _module.DList.nodes (T@U) T@U)
(declare-fun _module.DList.freeStack (T@U) Int)
(declare-fun _module.DList.s (T@U) T@U)
(declare-fun _module.DList.f (T@U) T@U)
(declare-fun _module.DList.g (T@U) T@U)
(declare-fun |$IsA#_module.DList| (T@U) Bool)
(declare-fun |_module.DList#Equal| (T@U T@U) Bool)
(declare-fun Tclass._module.__default () T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun _module.__default.Dec (Int Int) Int)
(declare-fun |_module.__default.Dec#canCall| (Int Int) Bool)
(declare-fun |_module.__default.Dec#requires| (Int Int) Bool)
(declare-fun _module.__default.Add (Int Int) Int)
(declare-fun |_module.__default.Add#canCall| (Int Int) Bool)
(declare-fun |_module.__default.Add#requires| (Int Int) Bool)
(declare-fun _module.__default.Sub (Int Int) Int)
(declare-fun |_module.__default.Sub#canCall| (Int Int) Bool)
(declare-fun |_module.__default.Sub#requires| (Int Int) Bool)
(declare-fun _module.__default.SeqRemove (T@U T@U Int) T@U)
(declare-fun |_module.__default.SeqRemove#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.SeqRemove#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.SeqInsert (T@U T@U Int T@U) T@U)
(declare-fun |_module.__default.SeqInsert#canCall| (T@U T@U Int T@U) Bool)
(declare-fun |_module.__default.SeqInsert#requires| (T@U T@U Int T@U) Bool)
(declare-fun _module.__default.SeqInit (T@U Int T@U) T@U)
(declare-fun |_module.__default.SeqInit#canCall| (T@U Int T@U) Bool)
(declare-fun |_module.__default.SeqInit#requires| (T@U Int T@U) Bool)
(declare-fun _module.__default.seq__get (T@U T@U Int) T@U)
(declare-fun |_module.__default.seq__get#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.seq__get#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.seq__set (T@U T@U Int T@U) T@U)
(declare-fun |_module.__default.seq__set#canCall| (T@U T@U Int T@U) Bool)
(declare-fun |_module.__default.seq__set#requires| (T@U T@U Int T@U) Bool)
(declare-fun _module.__default.seq_length (T@U T@U) Int)
(declare-fun |_module.__default.seq_length#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.seq_length#requires| (T@U T@U) Bool)
(declare-fun _module.__default.seq_empty (T@U) T@U)
(declare-fun |_module.__default.seq_empty#canCall| (T@U) Bool)
(declare-fun |_module.__default.seq_empty#requires| (T@U) Bool)
(declare-fun _module.__default.seq_alloc (T@U Int T@U) T@U)
(declare-fun |_module.__default.seq_alloc#canCall| (T@U Int T@U) Bool)
(declare-fun |_module.__default.seq_alloc#requires| (T@U Int T@U) Bool)
(declare-fun _module.__default.seq_free (T@U T@U) T@U)
(declare-fun |_module.__default.seq_free#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.seq_free#requires| (T@U T@U) Bool)
(declare-fun _module.__default.seq_unleash (T@U T@U) T@U)
(declare-fun |_module.__default.seq_unleash#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.seq_unleash#requires| (T@U T@U) Bool)
(declare-fun _module.__default.Invs (T@U T@U Int T@U T@U T@U) Bool)
(declare-fun |_module.__default.Invs#canCall| (T@U T@U Int T@U T@U T@U) Bool)
(declare-fun |_module.__default.Invs#requires| (T@U T@U Int T@U T@U T@U) Bool)
(declare-fun _module.__default.Inv (T@U T@U) Bool)
(declare-fun |_module.__default.Inv#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.Inv#requires| (T@U T@U) Bool)
(declare-fun _module.__default.Seq (T@U T@U) T@U)
(declare-fun |_module.__default.Seq#canCall| (T@U T@U) Bool)
(declare-fun |_module.__default.Seq#requires| (T@U T@U) Bool)
(declare-fun _module.__default.ValidPtr (T@U T@U Int) Bool)
(declare-fun |_module.__default.ValidPtr#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.ValidPtr#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.MaybePtr (T@U T@U Int) Bool)
(declare-fun |_module.__default.MaybePtr#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.MaybePtr#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.Index (T@U T@U Int) Int)
(declare-fun |_module.__default.Index#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.Index#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.IndexHi (T@U T@U Int) Int)
(declare-fun |_module.__default.IndexHi#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.IndexHi#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.Get (T@U T@U Int) T@U)
(declare-fun |_module.__default.Get#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.Get#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.Next (T@U T@U Int) Int)
(declare-fun |_module.__default.Next#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.Next#requires| (T@U T@U Int) Bool)
(declare-fun _module.__default.Prev (T@U T@U Int) Int)
(declare-fun |_module.__default.Prev#canCall| (T@U T@U Int) Bool)
(declare-fun |_module.__default.Prev#requires| (T@U T@U Int) Bool)
(declare-fun MapType6Type (T@T T@T) T@T)
(declare-fun MapType6TypeInv0 (T@T) T@T)
(declare-fun MapType6TypeInv1 (T@T) T@T)
(declare-fun MapType6Select (T@U T@U T@U) T@U)
(declare-fun MapType6Store (T@U T@U T@U T@U) T@U)
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
(declare-fun |lambda#10| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#11| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#12| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#13| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#14| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#15| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#16| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#17| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#18| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#19| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#20| (T@U T@U T@U Bool) T@U)
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
(declare-fun |lambda#33| (Int Int Int) T@U)
(declare-fun |lambda#34| (T@U) T@U)
(declare-fun |lambda#35| (Bool) T@U)
(declare-fun |lambda#36| (T@U) T@U)
(declare-fun |lambda#37| (T@U) T@U)
(declare-fun |lambda#53| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#54| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#55| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#56| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#57| (Int T@U Int) T@U)
(declare-fun |lambda#58| (T@U Int Int) T@U)
(declare-fun |lambda#77| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#78| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#79| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#80| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#81| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#82| (T@U Int Int T@U Int T@U Int T@U) T@U)
(declare-fun |lambda#102| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#103| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#104| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#105| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#106| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#107| (Int Int Int T@U T@U Int T@U) T@U)
(declare-fun |lambda#127| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#128| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#129| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#130| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#131| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#132| (Int Int T@U Int T@U Int T@U) T@U)
(declare-fun |lambda#152| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#153| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#154| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#155| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#156| (T@U T@U T@U Bool) T@U)
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
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (Ctor TyType) 6) (= (type TBool) TyType)) (= (type TChar) TyType)) (= (type TInt) TyType)) (= (type TReal) TyType)) (= (type TORDINAL) TyType)) (= (Ctor TyTagType) 7)) (= (type TagBool) TyTagType)) (= (type TagChar) TyTagType)) (= (type TagInt) TyTagType)) (= (type TagReal) TyTagType)) (= (type TagORDINAL) TyTagType)) (= (type TagSet) TyTagType)) (= (type TagISet) TyTagType)) (= (type TagMultiSet) TyTagType)) (= (type TagSeq) TyTagType)) (= (type TagMap) TyTagType)) (= (type TagIMap) TyTagType)) (= (type TagClass) TyTagType)) (= (Ctor ClassNameType) 8)) (= (type class._System.int) ClassNameType)) (= (type class._System.bool) ClassNameType)) (= (type class._System.set) ClassNameType)) (= (type class._System.seq) ClassNameType)) (= (type class._System.multiset) ClassNameType)) (forall ((arg0@@11 T@T) ) (! (= (Ctor (FieldType arg0@@11)) 9)
 :qid |ctor:FieldType|
))) (forall ((arg0@@12 T@T) ) (! (= (FieldTypeInv0 (FieldType arg0@@12)) arg0@@12)
 :qid |typeInv:FieldTypeInv0|
 :pattern ( (FieldType arg0@@12))
))) (= (type alloc) (FieldType boolType))) (= (Ctor NameFamilyType) 10)) (= (type allocName) NameFamilyType)) (= (type Tagclass._System.nat) TyTagType)) (= (type class._System.object?) ClassNameType)) (= (type Tagclass._System.object?) TyTagType)) (= (type Tagclass._System.object) TyTagType)) (= (type class._System.array?) ClassNameType)) (= (type Tagclass._System.array?) TyTagType)) (= (type Tagclass._System.array) TyTagType)) (= (type Tagclass._System.___hFunc1) TyTagType)) (= (type Tagclass._System.___hPartialFunc1) TyTagType)) (= (type Tagclass._System.___hTotalFunc1) TyTagType)) (= (type Tagclass._System.___hFunc0) TyTagType)) (= (type Tagclass._System.___hPartialFunc0) TyTagType)) (= (type Tagclass._System.___hTotalFunc0) TyTagType)) (= (type Tagclass._System.___hFunc2) TyTagType)) (= (type Tagclass._System.___hPartialFunc2) TyTagType)) (= (type Tagclass._System.___hTotalFunc2) TyTagType)) (= (type Tagclass._System.___hFunc3) TyTagType)) (= (type Tagclass._System.___hPartialFunc3) TyTagType)) (= (type Tagclass._System.___hTotalFunc3) TyTagType)) (= (Ctor DtCtorIdType) 11)) (= (type |##_System._tuple#0._#Make0|) DtCtorIdType)) (= (type Tagclass._System.Tuple0) TyTagType)) (= (type class._System.Tuple0) ClassNameType)) (= (type Tagclass._System.___hFunc5) TyTagType)) (= (type Tagclass._System.___hPartialFunc5) TyTagType)) (= (type Tagclass._System.___hTotalFunc5) TyTagType)) (= (type |##_System._tuple#2._#Make2|) DtCtorIdType)) (= (type Tagclass._System.Tuple2) TyTagType)) (= (type class._System.Tuple2) ClassNameType)) (= (type |##_module.Option.None|) DtCtorIdType)) (= (type Tagclass._module.Option) TyTagType)) (= (type |##_module.Option.Some|) DtCtorIdType)) (= (type class._module.Option) ClassNameType)) (= (type |##_module.Node.Node|) DtCtorIdType)) (= (type Tagclass._module.Node) TyTagType)) (= (type class._module.Node) ClassNameType)) (= (type |##_module.DList.DList|) DtCtorIdType)) (= (type Tagclass._module.DList) TyTagType)) (= (type class._module.DList) ClassNameType)) (= (type class._module.__default) ClassNameType)) (= (type Tagclass._module.__default) TyTagType)))
(assert (distinct TBool TChar TInt TReal TORDINAL TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass class._System.int class._System.bool class._System.set class._System.seq class._System.multiset alloc allocName Tagclass._System.nat class._System.object? Tagclass._System.object? Tagclass._System.object class._System.array? Tagclass._System.array? Tagclass._System.array Tagclass._System.___hFunc1 Tagclass._System.___hPartialFunc1 Tagclass._System.___hTotalFunc1 Tagclass._System.___hFunc0 Tagclass._System.___hPartialFunc0 Tagclass._System.___hTotalFunc0 Tagclass._System.___hFunc2 Tagclass._System.___hPartialFunc2 Tagclass._System.___hTotalFunc2 Tagclass._System.___hFunc3 Tagclass._System.___hPartialFunc3 Tagclass._System.___hTotalFunc3 |##_System._tuple#0._#Make0| Tagclass._System.Tuple0 class._System.Tuple0 Tagclass._System.___hFunc5 Tagclass._System.___hPartialFunc5 Tagclass._System.___hTotalFunc5 |##_System._tuple#2._#Make2| Tagclass._System.Tuple2 class._System.Tuple2 |##_module.Option.None| Tagclass._module.Option |##_module.Option.Some| class._module.Option |##_module.Node.Node| Tagclass._module.Node class._module.Node |##_module.DList.DList| Tagclass._module.DList class._module.DList class._module.__default Tagclass._module.__default)
)
(assert $$Language$Dafny)
(assert (forall ((arg0@@13 Int) ) (! (= (type (TBitvector arg0@@13)) TyType)
 :qid |funType:TBitvector|
 :pattern ( (TBitvector arg0@@13))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |DafnyPre.32:15|
 :skolemid |310|
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
 :skolemid |311|
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
 :skolemid |312|
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
 :skolemid |313|
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
 :skolemid |314|
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
 :skolemid |315|
 :pattern ( (TMap t@@3 u))
)))
(assert (forall ((arg0@@24 T@U) ) (! (= (type (Inv1_TMap arg0@@24)) TyType)
 :qid |funType:Inv1_TMap|
 :pattern ( (Inv1_TMap arg0@@24))
)))
(assert (forall ((t@@4 T@U) (u@@0 T@U) ) (!  (=> (and (= (type t@@4) TyType) (= (type u@@0) TyType)) (= (Inv1_TMap (TMap t@@4 u@@0)) u@@0))
 :qid |DafnyPre.44:15|
 :skolemid |316|
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
 :skolemid |317|
 :pattern ( (TIMap t@@5 u@@1))
)))
(assert (forall ((arg0@@27 T@U) ) (! (= (type (Inv1_TIMap arg0@@27)) TyType)
 :qid |funType:Inv1_TIMap|
 :pattern ( (Inv1_TIMap arg0@@27))
)))
(assert (forall ((t@@6 T@U) (u@@2 T@U) ) (!  (=> (and (= (type t@@6) TyType) (= (type u@@2) TyType)) (= (Inv1_TIMap (TIMap t@@6 u@@2)) u@@2))
 :qid |DafnyPre.48:15|
 :skolemid |318|
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
 :skolemid |319|
 :pattern ( (TSet t@@7))
)))
(assert (forall ((t@@8 T@U) ) (!  (=> (= (type t@@8) TyType) (= (Tag (TISet t@@8)) TagISet))
 :qid |DafnyPre.75:15|
 :skolemid |320|
 :pattern ( (TISet t@@8))
)))
(assert (forall ((t@@9 T@U) ) (!  (=> (= (type t@@9) TyType) (= (Tag (TMultiSet t@@9)) TagMultiSet))
 :qid |DafnyPre.76:15|
 :skolemid |321|
 :pattern ( (TMultiSet t@@9))
)))
(assert (forall ((t@@10 T@U) ) (!  (=> (= (type t@@10) TyType) (= (Tag (TSeq t@@10)) TagSeq))
 :qid |DafnyPre.77:15|
 :skolemid |322|
 :pattern ( (TSeq t@@10))
)))
(assert (forall ((t@@11 T@U) (u@@3 T@U) ) (!  (=> (and (= (type t@@11) TyType) (= (type u@@3) TyType)) (= (Tag (TMap t@@11 u@@3)) TagMap))
 :qid |DafnyPre.78:15|
 :skolemid |323|
 :pattern ( (TMap t@@11 u@@3))
)))
(assert (forall ((t@@12 T@U) (u@@4 T@U) ) (!  (=> (and (= (type t@@12) TyType) (= (type u@@4) TyType)) (= (Tag (TIMap t@@12 u@@4)) TagIMap))
 :qid |DafnyPre.79:15|
 :skolemid |324|
 :pattern ( (TIMap t@@12 u@@4))
)))
(assert (forall ((arg0@@29 T@U) ) (! (let ((T (type arg0@@29)))
(= (type (Lit arg0@@29)) T))
 :qid |funType:Lit|
 :pattern ( (Lit arg0@@29))
)))
(assert (forall ((x@@8 T@U) ) (! (= (Lit x@@8) x@@8)
 :qid |DafnyPre.84:29|
 :skolemid |325|
 :pattern ( (Lit x@@8))
)))
(assert  (and (= (Ctor BoxType) 12) (forall ((arg0@@30 T@U) ) (! (= (type ($Box arg0@@30)) BoxType)
 :qid |funType:$Box|
 :pattern ( ($Box arg0@@30))
))))
(assert (forall ((x@@9 T@U) ) (! (= ($Box (Lit x@@9)) (Lit ($Box x@@9)))
 :qid |DafnyPre.85:18|
 :skolemid |326|
 :pattern ( ($Box (Lit x@@9)))
)))
(assert (forall ((x@@10 T@U) ) (!  (=> (= (type x@@10) intType) (= ($Box x@@10) (Lit ($Box x@@10))))
 :qid |DafnyPre.91:15|
 :skolemid |327|
 :pattern ( ($Box x@@10))
)))
(assert (forall ((x@@11 Real) ) (! (= (LitReal x@@11) x@@11)
 :qid |DafnyPre.92:30|
 :skolemid |328|
 :pattern ( (LitReal x@@11))
)))
(assert (forall ((x@@12 Real) ) (! (= ($Box (real_2_U (LitReal x@@12))) (Lit ($Box (real_2_U x@@12))))
 :qid |DafnyPre.93:15|
 :skolemid |329|
 :pattern ( ($Box (real_2_U (LitReal x@@12))))
)))
(assert  (and (= (Ctor charType) 13) (forall ((arg0@@31 Int) ) (! (= (type (|char#FromInt| arg0@@31)) charType)
 :qid |funType:char#FromInt|
 :pattern ( (|char#FromInt| arg0@@31))
))))
(assert (forall ((ch T@U) ) (!  (=> (= (type ch) charType) (and (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (<= 0 (|char#ToInt| ch))) (< (|char#ToInt| ch) 65536)))
 :qid |DafnyPre.102:15|
 :skolemid |330|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((n Int) ) (!  (=> (and (<= 0 n) (< n 65536)) (= (|char#ToInt| (|char#FromInt| n)) n))
 :qid |DafnyPre.106:15|
 :skolemid |331|
 :pattern ( (|char#FromInt| n))
)))
(assert (forall ((arg0@@32 T@U) (arg1@@1 T@U) ) (! (= (type (|char#Plus| arg0@@32 arg1@@1)) charType)
 :qid |funType:char#Plus|
 :pattern ( (|char#Plus| arg0@@32 arg1@@1))
)))
(assert (forall ((a T@U) (b T@U) ) (!  (=> (and (= (type a) charType) (= (type b) charType)) (= (|char#Plus| a b) (|char#FromInt| (+ (|char#ToInt| a) (|char#ToInt| b)))))
 :qid |DafnyPre.112:15|
 :skolemid |332|
 :pattern ( (|char#Plus| a b))
)))
(assert (forall ((arg0@@33 T@U) (arg1@@2 T@U) ) (! (= (type (|char#Minus| arg0@@33 arg1@@2)) charType)
 :qid |funType:char#Minus|
 :pattern ( (|char#Minus| arg0@@33 arg1@@2))
)))
(assert (forall ((a@@0 T@U) (b@@0 T@U) ) (!  (=> (and (= (type a@@0) charType) (= (type b@@0) charType)) (= (|char#Minus| a@@0 b@@0) (|char#FromInt| (- (|char#ToInt| a@@0) (|char#ToInt| b@@0)))))
 :qid |DafnyPre.115:15|
 :skolemid |333|
 :pattern ( (|char#Minus| a@@0 b@@0))
)))
(assert (forall ((T@@0 T@T) (arg0@@34 T@U) ) (! (= (type ($Unbox T@@0 arg0@@34)) T@@0)
 :qid |funType:$Unbox|
 :pattern ( ($Unbox T@@0 arg0@@34))
)))
(assert (forall ((x@@13 T@U) ) (! (let ((T@@1 (type x@@13)))
(= ($Unbox T@@1 ($Box x@@13)) x@@13))
 :qid |DafnyPre.136:18|
 :skolemid |334|
 :pattern ( ($Box x@@13))
)))
(assert (forall ((bx T@U) ) (!  (=> (and (= (type bx) BoxType) ($IsBox bx TInt)) (and (= ($Box ($Unbox intType bx)) bx) ($Is ($Unbox intType bx) TInt)))
 :qid |DafnyPre.138:15|
 :skolemid |335|
 :pattern ( ($IsBox bx TInt))
)))
(assert (forall ((bx@@0 T@U) ) (!  (=> (and (= (type bx@@0) BoxType) ($IsBox bx@@0 TReal)) (and (= ($Box ($Unbox realType bx@@0)) bx@@0) ($Is ($Unbox realType bx@@0) TReal)))
 :qid |DafnyPre.141:15|
 :skolemid |336|
 :pattern ( ($IsBox bx@@0 TReal))
)))
(assert (forall ((bx@@1 T@U) ) (!  (=> (and (= (type bx@@1) BoxType) ($IsBox bx@@1 TBool)) (and (= ($Box ($Unbox boolType bx@@1)) bx@@1) ($Is ($Unbox boolType bx@@1) TBool)))
 :qid |DafnyPre.144:15|
 :skolemid |337|
 :pattern ( ($IsBox bx@@1 TBool))
)))
(assert (forall ((bx@@2 T@U) ) (!  (=> (and (= (type bx@@2) BoxType) ($IsBox bx@@2 TChar)) (and (= ($Box ($Unbox charType bx@@2)) bx@@2) ($Is ($Unbox charType bx@@2) TChar)))
 :qid |DafnyPre.147:15|
 :skolemid |338|
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
 :skolemid |339|
 :pattern ( ($IsBox bx@@3 (TSet t@@13)))
)))
(assert (forall ((bx@@4 T@U) (t@@14 T@U) ) (!  (=> (and (and (= (type bx@@4) BoxType) (= (type t@@14) TyType)) ($IsBox bx@@4 (TISet t@@14))) (and (= ($Box ($Unbox (MapType0Type BoxType boolType) bx@@4)) bx@@4) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@4) (TISet t@@14))))
 :qid |DafnyPre.153:15|
 :skolemid |340|
 :pattern ( ($IsBox bx@@4 (TISet t@@14)))
)))
(assert (forall ((bx@@5 T@U) (t@@15 T@U) ) (!  (=> (and (and (= (type bx@@5) BoxType) (= (type t@@15) TyType)) ($IsBox bx@@5 (TMultiSet t@@15))) (and (= ($Box ($Unbox (MapType0Type BoxType intType) bx@@5)) bx@@5) ($Is ($Unbox (MapType0Type BoxType intType) bx@@5) (TMultiSet t@@15))))
 :qid |DafnyPre.156:15|
 :skolemid |341|
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
 :skolemid |342|
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
 :skolemid |343|
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
 :skolemid |344|
 :pattern ( ($IsBox bx@@8 (TIMap s@@0 t@@18)))
)))
(assert (forall ((v T@U) (t@@19 T@U) ) (!  (=> (= (type t@@19) TyType) (and (=> ($IsBox ($Box v) t@@19) ($Is v t@@19)) (=> ($Is v t@@19) ($IsBox ($Box v) t@@19))))
 :qid |DafnyPre.169:18|
 :skolemid |345|
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
 :skolemid |346|
 :pattern ( ($IsAllocBox ($Box v@@0) t@@20 h))
)))
(assert (forall ((v@@1 T@U) ) (!  (=> (= (type v@@1) intType) ($Is v@@1 TInt))
 :qid |DafnyPre.190:14|
 :skolemid |347|
 :pattern ( ($Is v@@1 TInt))
)))
(assert (forall ((v@@2 T@U) ) (!  (=> (= (type v@@2) realType) ($Is v@@2 TReal))
 :qid |DafnyPre.191:14|
 :skolemid |348|
 :pattern ( ($Is v@@2 TReal))
)))
(assert (forall ((v@@3 T@U) ) (!  (=> (= (type v@@3) boolType) ($Is v@@3 TBool))
 :qid |DafnyPre.192:14|
 :skolemid |349|
 :pattern ( ($Is v@@3 TBool))
)))
(assert (forall ((v@@4 T@U) ) (!  (=> (= (type v@@4) charType) ($Is v@@4 TChar))
 :qid |DafnyPre.193:14|
 :skolemid |350|
 :pattern ( ($Is v@@4 TChar))
)))
(assert (forall ((v@@5 T@U) ) (!  (=> (= (type v@@5) BoxType) ($Is v@@5 TORDINAL))
 :qid |DafnyPre.194:14|
 :skolemid |351|
 :pattern ( ($Is v@@5 TORDINAL))
)))
(assert (forall ((h@@0 T@U) (v@@6 T@U) ) (!  (=> (and (= (type h@@0) (MapType0Type refType MapType1Type)) (= (type v@@6) intType)) ($IsAlloc v@@6 TInt h@@0))
 :qid |DafnyPre.196:14|
 :skolemid |352|
 :pattern ( ($IsAlloc v@@6 TInt h@@0))
)))
(assert (forall ((h@@1 T@U) (v@@7 T@U) ) (!  (=> (and (= (type h@@1) (MapType0Type refType MapType1Type)) (= (type v@@7) realType)) ($IsAlloc v@@7 TReal h@@1))
 :qid |DafnyPre.197:14|
 :skolemid |353|
 :pattern ( ($IsAlloc v@@7 TReal h@@1))
)))
(assert (forall ((h@@2 T@U) (v@@8 T@U) ) (!  (=> (and (= (type h@@2) (MapType0Type refType MapType1Type)) (= (type v@@8) boolType)) ($IsAlloc v@@8 TBool h@@2))
 :qid |DafnyPre.198:14|
 :skolemid |354|
 :pattern ( ($IsAlloc v@@8 TBool h@@2))
)))
(assert (forall ((h@@3 T@U) (v@@9 T@U) ) (!  (=> (and (= (type h@@3) (MapType0Type refType MapType1Type)) (= (type v@@9) charType)) ($IsAlloc v@@9 TChar h@@3))
 :qid |DafnyPre.199:14|
 :skolemid |355|
 :pattern ( ($IsAlloc v@@9 TChar h@@3))
)))
(assert (forall ((h@@4 T@U) (v@@10 T@U) ) (!  (=> (and (= (type h@@4) (MapType0Type refType MapType1Type)) (= (type v@@10) BoxType)) ($IsAlloc v@@10 TORDINAL h@@4))
 :qid |DafnyPre.200:14|
 :skolemid |356|
 :pattern ( ($IsAlloc v@@10 TORDINAL h@@4))
)))
(assert (forall ((v@@11 T@U) (t0 T@U) ) (!  (=> (and (= (type v@@11) (MapType0Type BoxType boolType)) (= (type t0) TyType)) (and (=> ($Is v@@11 (TSet t0)) (forall ((bx@@9 T@U) ) (!  (=> (and (= (type bx@@9) BoxType) (U_2_bool (MapType0Select v@@11 bx@@9))) ($IsBox bx@@9 t0))
 :qid |DafnyPre.204:11|
 :skolemid |357|
 :pattern ( (MapType0Select v@@11 bx@@9))
))) (=> (forall ((bx@@10 T@U) ) (!  (=> (and (= (type bx@@10) BoxType) (U_2_bool (MapType0Select v@@11 bx@@10))) ($IsBox bx@@10 t0))
 :qid |DafnyPre.204:11|
 :skolemid |357|
 :pattern ( (MapType0Select v@@11 bx@@10))
)) ($Is v@@11 (TSet t0)))))
 :qid |DafnyPre.202:15|
 :skolemid |358|
 :pattern ( ($Is v@@11 (TSet t0)))
)))
(assert (forall ((v@@12 T@U) (t0@@0 T@U) ) (!  (=> (and (= (type v@@12) (MapType0Type BoxType boolType)) (= (type t0@@0) TyType)) (and (=> ($Is v@@12 (TISet t0@@0)) (forall ((bx@@11 T@U) ) (!  (=> (and (= (type bx@@11) BoxType) (U_2_bool (MapType0Select v@@12 bx@@11))) ($IsBox bx@@11 t0@@0))
 :qid |DafnyPre.208:11|
 :skolemid |359|
 :pattern ( (MapType0Select v@@12 bx@@11))
))) (=> (forall ((bx@@12 T@U) ) (!  (=> (and (= (type bx@@12) BoxType) (U_2_bool (MapType0Select v@@12 bx@@12))) ($IsBox bx@@12 t0@@0))
 :qid |DafnyPre.208:11|
 :skolemid |359|
 :pattern ( (MapType0Select v@@12 bx@@12))
)) ($Is v@@12 (TISet t0@@0)))))
 :qid |DafnyPre.206:15|
 :skolemid |360|
 :pattern ( ($Is v@@12 (TISet t0@@0)))
)))
(assert (forall ((v@@13 T@U) (t0@@1 T@U) ) (!  (=> (and (= (type v@@13) (MapType0Type BoxType intType)) (= (type t0@@1) TyType)) (and (=> ($Is v@@13 (TMultiSet t0@@1)) (forall ((bx@@13 T@U) ) (!  (=> (and (= (type bx@@13) BoxType) (< 0 (U_2_int (MapType0Select v@@13 bx@@13)))) ($IsBox bx@@13 t0@@1))
 :qid |DafnyPre.212:11|
 :skolemid |361|
 :pattern ( (MapType0Select v@@13 bx@@13))
))) (=> (forall ((bx@@14 T@U) ) (!  (=> (and (= (type bx@@14) BoxType) (< 0 (U_2_int (MapType0Select v@@13 bx@@14)))) ($IsBox bx@@14 t0@@1))
 :qid |DafnyPre.212:11|
 :skolemid |361|
 :pattern ( (MapType0Select v@@13 bx@@14))
)) ($Is v@@13 (TMultiSet t0@@1)))))
 :qid |DafnyPre.210:15|
 :skolemid |362|
 :pattern ( ($Is v@@13 (TMultiSet t0@@1)))
)))
(assert (forall ((v@@14 T@U) (t0@@2 T@U) ) (!  (=> (and (and (= (type v@@14) (MapType0Type BoxType intType)) (= (type t0@@2) TyType)) ($Is v@@14 (TMultiSet t0@@2))) ($IsGoodMultiSet v@@14))
 :qid |DafnyPre.214:15|
 :skolemid |363|
 :pattern ( ($Is v@@14 (TMultiSet t0@@2)))
)))
(assert (forall ((arg0@@50 T@U) (arg1@@16 Int) ) (! (let ((T@@2 (SeqTypeInv0 (type arg0@@50))))
(= (type (|Seq#Index| arg0@@50 arg1@@16)) T@@2))
 :qid |funType:Seq#Index|
 :pattern ( (|Seq#Index| arg0@@50 arg1@@16))
)))
(assert (forall ((v@@15 T@U) (t0@@3 T@U) ) (!  (=> (and (= (type v@@15) (SeqType BoxType)) (= (type t0@@3) TyType)) (and (=> ($Is v@@15 (TSeq t0@@3)) (forall ((i Int) ) (!  (=> (and (<= 0 i) (< i (|Seq#Length| v@@15))) ($IsBox (|Seq#Index| v@@15 i) t0@@3))
 :qid |DafnyPre.218:11|
 :skolemid |364|
 :pattern ( (|Seq#Index| v@@15 i))
))) (=> (forall ((i@@0 Int) ) (!  (=> (and (<= 0 i@@0) (< i@@0 (|Seq#Length| v@@15))) ($IsBox (|Seq#Index| v@@15 i@@0) t0@@3))
 :qid |DafnyPre.218:11|
 :skolemid |364|
 :pattern ( (|Seq#Index| v@@15 i@@0))
)) ($Is v@@15 (TSeq t0@@3)))))
 :qid |DafnyPre.216:15|
 :skolemid |365|
 :pattern ( ($Is v@@15 (TSeq t0@@3)))
)))
(assert (forall ((v@@16 T@U) (t0@@4 T@U) (h@@5 T@U) ) (!  (=> (and (and (= (type v@@16) (MapType0Type BoxType boolType)) (= (type t0@@4) TyType)) (= (type h@@5) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@16 (TSet t0@@4) h@@5) (forall ((bx@@15 T@U) ) (!  (=> (and (= (type bx@@15) BoxType) (U_2_bool (MapType0Select v@@16 bx@@15))) ($IsAllocBox bx@@15 t0@@4 h@@5))
 :qid |DafnyPre.223:11|
 :skolemid |366|
 :pattern ( (MapType0Select v@@16 bx@@15))
))) (=> (forall ((bx@@16 T@U) ) (!  (=> (and (= (type bx@@16) BoxType) (U_2_bool (MapType0Select v@@16 bx@@16))) ($IsAllocBox bx@@16 t0@@4 h@@5))
 :qid |DafnyPre.223:11|
 :skolemid |366|
 :pattern ( (MapType0Select v@@16 bx@@16))
)) ($IsAlloc v@@16 (TSet t0@@4) h@@5))))
 :qid |DafnyPre.221:15|
 :skolemid |367|
 :pattern ( ($IsAlloc v@@16 (TSet t0@@4) h@@5))
)))
(assert (forall ((v@@17 T@U) (t0@@5 T@U) (h@@6 T@U) ) (!  (=> (and (and (= (type v@@17) (MapType0Type BoxType boolType)) (= (type t0@@5) TyType)) (= (type h@@6) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@17 (TISet t0@@5) h@@6) (forall ((bx@@17 T@U) ) (!  (=> (and (= (type bx@@17) BoxType) (U_2_bool (MapType0Select v@@17 bx@@17))) ($IsAllocBox bx@@17 t0@@5 h@@6))
 :qid |DafnyPre.227:11|
 :skolemid |368|
 :pattern ( (MapType0Select v@@17 bx@@17))
))) (=> (forall ((bx@@18 T@U) ) (!  (=> (and (= (type bx@@18) BoxType) (U_2_bool (MapType0Select v@@17 bx@@18))) ($IsAllocBox bx@@18 t0@@5 h@@6))
 :qid |DafnyPre.227:11|
 :skolemid |368|
 :pattern ( (MapType0Select v@@17 bx@@18))
)) ($IsAlloc v@@17 (TISet t0@@5) h@@6))))
 :qid |DafnyPre.225:15|
 :skolemid |369|
 :pattern ( ($IsAlloc v@@17 (TISet t0@@5) h@@6))
)))
(assert (forall ((v@@18 T@U) (t0@@6 T@U) (h@@7 T@U) ) (!  (=> (and (and (= (type v@@18) (MapType0Type BoxType intType)) (= (type t0@@6) TyType)) (= (type h@@7) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7) (forall ((bx@@19 T@U) ) (!  (=> (and (= (type bx@@19) BoxType) (< 0 (U_2_int (MapType0Select v@@18 bx@@19)))) ($IsAllocBox bx@@19 t0@@6 h@@7))
 :qid |DafnyPre.231:11|
 :skolemid |370|
 :pattern ( (MapType0Select v@@18 bx@@19))
))) (=> (forall ((bx@@20 T@U) ) (!  (=> (and (= (type bx@@20) BoxType) (< 0 (U_2_int (MapType0Select v@@18 bx@@20)))) ($IsAllocBox bx@@20 t0@@6 h@@7))
 :qid |DafnyPre.231:11|
 :skolemid |370|
 :pattern ( (MapType0Select v@@18 bx@@20))
)) ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7))))
 :qid |DafnyPre.229:15|
 :skolemid |371|
 :pattern ( ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7))
)))
(assert (forall ((v@@19 T@U) (t0@@7 T@U) (h@@8 T@U) ) (!  (=> (and (and (= (type v@@19) (SeqType BoxType)) (= (type t0@@7) TyType)) (= (type h@@8) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@19 (TSeq t0@@7) h@@8) (forall ((i@@1 Int) ) (!  (=> (and (<= 0 i@@1) (< i@@1 (|Seq#Length| v@@19))) ($IsAllocBox (|Seq#Index| v@@19 i@@1) t0@@7 h@@8))
 :qid |DafnyPre.235:11|
 :skolemid |372|
 :pattern ( (|Seq#Index| v@@19 i@@1))
))) (=> (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (|Seq#Length| v@@19))) ($IsAllocBox (|Seq#Index| v@@19 i@@2) t0@@7 h@@8))
 :qid |DafnyPre.235:11|
 :skolemid |372|
 :pattern ( (|Seq#Index| v@@19 i@@2))
)) ($IsAlloc v@@19 (TSeq t0@@7) h@@8))))
 :qid |DafnyPre.233:15|
 :skolemid |373|
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
 :skolemid |374|
 :pattern ( (MapType0Select (|Map#Elements| v@@20) bx@@21))
 :pattern ( (MapType0Select (|Map#Domain| v@@20) bx@@21))
))) (=> (forall ((bx@@22 T@U) ) (!  (=> (and (= (type bx@@22) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@20) bx@@22))) (and ($IsBox (MapType0Select (|Map#Elements| v@@20) bx@@22) t1) ($IsBox bx@@22 t0@@8)))
 :qid |DafnyPre.242:19|
 :skolemid |374|
 :pattern ( (MapType0Select (|Map#Elements| v@@20) bx@@22))
 :pattern ( (MapType0Select (|Map#Domain| v@@20) bx@@22))
)) ($Is v@@20 (TMap t0@@8 t1)))))
 :qid |DafnyPre.239:15|
 :skolemid |375|
 :pattern ( ($Is v@@20 (TMap t0@@8 t1)))
)))
(assert (forall ((v@@21 T@U) (t0@@9 T@U) (t1@@0 T@U) (h@@9 T@U) ) (!  (=> (and (and (and (= (type v@@21) (MapType BoxType BoxType)) (= (type t0@@9) TyType)) (= (type t1@@0) TyType)) (= (type h@@9) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9) (forall ((bx@@23 T@U) ) (!  (=> (and (= (type bx@@23) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@21) bx@@23))) (and ($IsAllocBox (MapType0Select (|Map#Elements| v@@21) bx@@23) t1@@0 h@@9) ($IsAllocBox bx@@23 t0@@9 h@@9)))
 :qid |DafnyPre.250:19|
 :skolemid |376|
 :pattern ( (MapType0Select (|Map#Elements| v@@21) bx@@23))
 :pattern ( (MapType0Select (|Map#Domain| v@@21) bx@@23))
))) (=> (forall ((bx@@24 T@U) ) (!  (=> (and (= (type bx@@24) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@21) bx@@24))) (and ($IsAllocBox (MapType0Select (|Map#Elements| v@@21) bx@@24) t1@@0 h@@9) ($IsAllocBox bx@@24 t0@@9 h@@9)))
 :qid |DafnyPre.250:19|
 :skolemid |376|
 :pattern ( (MapType0Select (|Map#Elements| v@@21) bx@@24))
 :pattern ( (MapType0Select (|Map#Domain| v@@21) bx@@24))
)) ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9))))
 :qid |DafnyPre.247:15|
 :skolemid |377|
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
 :skolemid |378|
 :pattern ( (MapType0Select (|IMap#Elements| v@@22) bx@@25))
 :pattern ( (MapType0Select (|IMap#Domain| v@@22) bx@@25))
))) (=> (forall ((bx@@26 T@U) ) (!  (=> (and (= (type bx@@26) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@22) bx@@26))) (and ($IsBox (MapType0Select (|IMap#Elements| v@@22) bx@@26) t1@@1) ($IsBox bx@@26 t0@@10)))
 :qid |DafnyPre.259:19|
 :skolemid |378|
 :pattern ( (MapType0Select (|IMap#Elements| v@@22) bx@@26))
 :pattern ( (MapType0Select (|IMap#Domain| v@@22) bx@@26))
)) ($Is v@@22 (TIMap t0@@10 t1@@1)))))
 :qid |DafnyPre.256:15|
 :skolemid |379|
 :pattern ( ($Is v@@22 (TIMap t0@@10 t1@@1)))
)))
(assert (forall ((v@@23 T@U) (t0@@11 T@U) (t1@@2 T@U) (h@@10 T@U) ) (!  (=> (and (and (and (= (type v@@23) (IMapType BoxType BoxType)) (= (type t0@@11) TyType)) (= (type t1@@2) TyType)) (= (type h@@10) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10) (forall ((bx@@27 T@U) ) (!  (=> (and (= (type bx@@27) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@23) bx@@27))) (and ($IsAllocBox (MapType0Select (|IMap#Elements| v@@23) bx@@27) t1@@2 h@@10) ($IsAllocBox bx@@27 t0@@11 h@@10)))
 :qid |DafnyPre.267:19|
 :skolemid |380|
 :pattern ( (MapType0Select (|IMap#Elements| v@@23) bx@@27))
 :pattern ( (MapType0Select (|IMap#Domain| v@@23) bx@@27))
))) (=> (forall ((bx@@28 T@U) ) (!  (=> (and (= (type bx@@28) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@23) bx@@28))) (and ($IsAllocBox (MapType0Select (|IMap#Elements| v@@23) bx@@28) t1@@2 h@@10) ($IsAllocBox bx@@28 t0@@11 h@@10)))
 :qid |DafnyPre.267:19|
 :skolemid |380|
 :pattern ( (MapType0Select (|IMap#Elements| v@@23) bx@@28))
 :pattern ( (MapType0Select (|IMap#Domain| v@@23) bx@@28))
)) ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10))))
 :qid |DafnyPre.264:15|
 :skolemid |381|
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
 :skolemid |382|
 :pattern ( (TypeTuple a@@1 b@@1))
)))
(assert (forall ((arg0@@58 T@U) ) (! (= (type (SetRef_to_SetBox arg0@@58)) (MapType0Type BoxType boolType))
 :qid |funType:SetRef_to_SetBox|
 :pattern ( (SetRef_to_SetBox arg0@@58))
)))
(assert (forall ((s@@1 T@U) (bx@@29 T@U) ) (!  (=> (and (= (type s@@1) (MapType0Type refType boolType)) (= (type bx@@29) BoxType)) (and (=> (U_2_bool (MapType0Select (SetRef_to_SetBox s@@1) bx@@29)) (U_2_bool (MapType0Select s@@1 ($Unbox refType bx@@29)))) (=> (U_2_bool (MapType0Select s@@1 ($Unbox refType bx@@29))) (U_2_bool (MapType0Select (SetRef_to_SetBox s@@1) bx@@29)))))
 :qid |DafnyPre.301:15|
 :skolemid |383|
 :pattern ( (MapType0Select (SetRef_to_SetBox s@@1) bx@@29))
)))
(assert (= (type Tclass._System.object?) TyType))
(assert (forall ((s@@2 T@U) ) (!  (=> (= (type s@@2) (MapType0Type refType boolType)) ($Is (SetRef_to_SetBox s@@2) (TSet Tclass._System.object?)))
 :qid |DafnyPre.303:15|
 :skolemid |384|
 :pattern ( (SetRef_to_SetBox s@@2))
)))
(assert (= (Ctor DatatypeTypeType) 20))
(assert (forall ((d T@U) ) (!  (=> (= (type d) DatatypeTypeType) (= (BoxRank ($Box d)) (DtRank d)))
 :qid |DafnyPre.322:15|
 :skolemid |385|
 :pattern ( (BoxRank ($Box d)))
)))
(assert (forall ((o T@U) ) (!  (=> (= (type o) BoxType) (<= 0 (|ORD#Offset| o)))
 :qid |DafnyPre.337:15|
 :skolemid |386|
 :pattern ( (|ORD#Offset| o))
)))
(assert (forall ((arg0@@59 Int) ) (! (= (type (|ORD#FromNat| arg0@@59)) BoxType)
 :qid |funType:ORD#FromNat|
 :pattern ( (|ORD#FromNat| arg0@@59))
)))
(assert (forall ((n@@0 Int) ) (!  (=> (<= 0 n@@0) (and (|ORD#IsNat| (|ORD#FromNat| n@@0)) (= (|ORD#Offset| (|ORD#FromNat| n@@0)) n@@0)))
 :qid |DafnyPre.343:15|
 :skolemid |387|
 :pattern ( (|ORD#FromNat| n@@0))
)))
(assert (forall ((o@@0 T@U) ) (!  (=> (and (= (type o@@0) BoxType) (|ORD#IsNat| o@@0)) (= o@@0 (|ORD#FromNat| (|ORD#Offset| o@@0))))
 :qid |DafnyPre.345:15|
 :skolemid |388|
 :pattern ( (|ORD#Offset| o@@0))
 :pattern ( (|ORD#IsNat| o@@0))
)))
(assert (forall ((o@@1 T@U) (p T@U) ) (!  (=> (and (= (type o@@1) BoxType) (= (type p) BoxType)) (and (and (and (=> (|ORD#Less| o@@1 p) (not (= o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (not (|ORD#IsNat| p))) (|ORD#Less| o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (|ORD#IsNat| p)) (and (=> (|ORD#Less| o@@1 p) (< (|ORD#Offset| o@@1) (|ORD#Offset| p))) (=> (< (|ORD#Offset| o@@1) (|ORD#Offset| p)) (|ORD#Less| o@@1 p))))) (=> (and (|ORD#Less| o@@1 p) (|ORD#IsNat| p)) (|ORD#IsNat| o@@1))))
 :qid |DafnyPre.349:15|
 :skolemid |389|
 :pattern ( (|ORD#Less| o@@1 p))
)))
(assert (forall ((o@@2 T@U) (p@@0 T@U) ) (!  (=> (and (= (type o@@2) BoxType) (= (type p@@0) BoxType)) (or (or (|ORD#Less| o@@2 p@@0) (= o@@2 p@@0)) (|ORD#Less| p@@0 o@@2)))
 :qid |DafnyPre.355:15|
 :skolemid |390|
 :pattern ( (|ORD#Less| o@@2 p@@0) (|ORD#Less| p@@0 o@@2))
)))
(assert (forall ((o@@3 T@U) (p@@1 T@U) (r T@U) ) (!  (=> (and (and (and (= (type o@@3) BoxType) (= (type p@@1) BoxType)) (= (type r) BoxType)) (and (|ORD#Less| o@@3 p@@1) (|ORD#Less| p@@1 r))) (|ORD#Less| o@@3 r))
 :qid |DafnyPre.358:15|
 :skolemid |391|
 :pattern ( (|ORD#Less| o@@3 p@@1) (|ORD#Less| p@@1 r))
 :pattern ( (|ORD#Less| o@@3 p@@1) (|ORD#Less| o@@3 r))
)))
(assert (forall ((o@@4 T@U) (p@@2 T@U) ) (!  (=> (and (= (type o@@4) BoxType) (= (type p@@2) BoxType)) (and (=> (|ORD#LessThanLimit| o@@4 p@@2) (|ORD#Less| o@@4 p@@2)) (=> (|ORD#Less| o@@4 p@@2) (|ORD#LessThanLimit| o@@4 p@@2))))
 :qid |DafnyPre.365:15|
 :skolemid |392|
 :pattern ( (|ORD#LessThanLimit| o@@4 p@@2))
)))
(assert (forall ((arg0@@60 T@U) (arg1@@18 T@U) ) (! (= (type (|ORD#Plus| arg0@@60 arg1@@18)) BoxType)
 :qid |funType:ORD#Plus|
 :pattern ( (|ORD#Plus| arg0@@60 arg1@@18))
)))
(assert (forall ((o@@5 T@U) (p@@3 T@U) ) (!  (=> (and (= (type o@@5) BoxType) (= (type p@@3) BoxType)) (and (=> (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)) (and (|ORD#IsNat| o@@5) (|ORD#IsNat| p@@3))) (=> (|ORD#IsNat| p@@3) (and (and (=> (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)) (|ORD#IsNat| o@@5)) (=> (|ORD#IsNat| o@@5) (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)))) (= (|ORD#Offset| (|ORD#Plus| o@@5 p@@3)) (+ (|ORD#Offset| o@@5) (|ORD#Offset| p@@3)))))))
 :qid |DafnyPre.369:15|
 :skolemid |393|
 :pattern ( (|ORD#Plus| o@@5 p@@3))
)))
(assert (forall ((o@@6 T@U) (p@@4 T@U) ) (!  (=> (and (= (type o@@6) BoxType) (= (type p@@4) BoxType)) (and (or (= o@@6 (|ORD#Plus| o@@6 p@@4)) (|ORD#Less| o@@6 (|ORD#Plus| o@@6 p@@4))) (or (= p@@4 (|ORD#Plus| o@@6 p@@4)) (|ORD#Less| p@@4 (|ORD#Plus| o@@6 p@@4)))))
 :qid |DafnyPre.374:15|
 :skolemid |394|
 :pattern ( (|ORD#Plus| o@@6 p@@4))
)))
(assert (forall ((o@@7 T@U) (p@@5 T@U) ) (!  (=> (and (= (type o@@7) BoxType) (= (type p@@5) BoxType)) (and (=> (= o@@7 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@7 p@@5) p@@5)) (=> (= p@@5 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@7 p@@5) o@@7))))
 :qid |DafnyPre.377:15|
 :skolemid |395|
 :pattern ( (|ORD#Plus| o@@7 p@@5))
)))
(assert (forall ((arg0@@61 T@U) (arg1@@19 T@U) ) (! (= (type (|ORD#Minus| arg0@@61 arg1@@19)) BoxType)
 :qid |funType:ORD#Minus|
 :pattern ( (|ORD#Minus| arg0@@61 arg1@@19))
)))
(assert (forall ((o@@8 T@U) (p@@6 T@U) ) (!  (=> (and (and (= (type o@@8) BoxType) (= (type p@@6) BoxType)) (and (|ORD#IsNat| p@@6) (<= (|ORD#Offset| p@@6) (|ORD#Offset| o@@8)))) (and (and (=> (|ORD#IsNat| (|ORD#Minus| o@@8 p@@6)) (|ORD#IsNat| o@@8)) (=> (|ORD#IsNat| o@@8) (|ORD#IsNat| (|ORD#Minus| o@@8 p@@6)))) (= (|ORD#Offset| (|ORD#Minus| o@@8 p@@6)) (- (|ORD#Offset| o@@8) (|ORD#Offset| p@@6)))))
 :qid |DafnyPre.382:15|
 :skolemid |396|
 :pattern ( (|ORD#Minus| o@@8 p@@6))
)))
(assert (forall ((o@@9 T@U) (p@@7 T@U) ) (!  (=> (and (and (= (type o@@9) BoxType) (= (type p@@7) BoxType)) (and (|ORD#IsNat| p@@7) (<= (|ORD#Offset| p@@7) (|ORD#Offset| o@@9)))) (or (and (= p@@7 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@9 p@@7) o@@9)) (and (not (= p@@7 (|ORD#FromNat| 0))) (|ORD#Less| (|ORD#Minus| o@@9 p@@7) o@@9))))
 :qid |DafnyPre.386:15|
 :skolemid |397|
 :pattern ( (|ORD#Minus| o@@9 p@@7))
)))
(assert (forall ((o@@10 T@U) (m@@5 Int) (n@@1 Int) ) (!  (=> (= (type o@@10) BoxType) (=> (and (<= 0 m@@5) (<= 0 n@@1)) (= (|ORD#Plus| (|ORD#Plus| o@@10 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n@@1)) (|ORD#Plus| o@@10 (|ORD#FromNat| (+ m@@5 n@@1))))))
 :qid |DafnyPre.392:15|
 :skolemid |398|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@10 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n@@1)))
)))
(assert (forall ((o@@11 T@U) (m@@6 Int) (n@@2 Int) ) (!  (=> (= (type o@@11) BoxType) (=> (and (and (<= 0 m@@6) (<= 0 n@@2)) (<= (+ m@@6 n@@2) (|ORD#Offset| o@@11))) (= (|ORD#Minus| (|ORD#Minus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@2)) (|ORD#Minus| o@@11 (|ORD#FromNat| (+ m@@6 n@@2))))))
 :qid |DafnyPre.397:15|
 :skolemid |399|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@2)))
)))
(assert (forall ((o@@12 T@U) (m@@7 Int) (n@@3 Int) ) (!  (=> (= (type o@@12) BoxType) (=> (and (and (<= 0 m@@7) (<= 0 n@@3)) (<= n@@3 (+ (|ORD#Offset| o@@12) m@@7))) (and (=> (<= 0 (- m@@7 n@@3)) (= (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)) (|ORD#Plus| o@@12 (|ORD#FromNat| (- m@@7 n@@3))))) (=> (<= (- m@@7 n@@3) 0) (= (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)) (|ORD#Minus| o@@12 (|ORD#FromNat| (- n@@3 m@@7))))))))
 :qid |DafnyPre.402:15|
 :skolemid |400|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)))
)))
(assert (forall ((o@@13 T@U) (m@@8 Int) (n@@4 Int) ) (!  (=> (= (type o@@13) BoxType) (=> (and (and (<= 0 m@@8) (<= 0 n@@4)) (<= n@@4 (+ (|ORD#Offset| o@@13) m@@8))) (and (=> (<= 0 (- m@@8 n@@4)) (= (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)) (|ORD#Minus| o@@13 (|ORD#FromNat| (- m@@8 n@@4))))) (=> (<= (- m@@8 n@@4) 0) (= (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)) (|ORD#Plus| o@@13 (|ORD#FromNat| (- n@@4 m@@8))))))))
 :qid |DafnyPre.408:15|
 :skolemid |401|
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
 :skolemid |402|
 :pattern ( (AtLayer f ly))
)))
(assert (forall ((arg0@@63 T@U) ) (! (= (type ($LS arg0@@63)) LayerTypeType)
 :qid |funType:$LS|
 :pattern ( ($LS arg0@@63))
)))
(assert (forall ((f@@0 T@U) (ly@@0 T@U) ) (! (let ((A@@1 (MapType0TypeInv1 (type f@@0))))
 (=> (and (= (type f@@0) (MapType0Type LayerTypeType A@@1)) (= (type ly@@0) LayerTypeType)) (= (AtLayer f@@0 ($LS ly@@0)) (AtLayer f@@0 ly@@0))))
 :qid |DafnyPre.433:18|
 :skolemid |403|
 :pattern ( (AtLayer f@@0 ($LS ly@@0)))
)))
(assert (forall ((arg0@@64 Int) ) (! (= (type (IndexField arg0@@64)) (FieldType BoxType))
 :qid |funType:IndexField|
 :pattern ( (IndexField arg0@@64))
)))
(assert (forall ((i@@3 Int) ) (! (= (FDim (IndexField i@@3)) 1)
 :qid |DafnyPre.444:15|
 :skolemid |404|
 :pattern ( (IndexField i@@3))
)))
(assert (forall ((i@@4 Int) ) (! (= (IndexField_Inverse (IndexField i@@4)) i@@4)
 :qid |DafnyPre.446:15|
 :skolemid |405|
 :pattern ( (IndexField i@@4))
)))
(assert (forall ((arg0@@65 T@U) (arg1@@21 Int) ) (! (= (type (MultiIndexField arg0@@65 arg1@@21)) (FieldType BoxType))
 :qid |funType:MultiIndexField|
 :pattern ( (MultiIndexField arg0@@65 arg1@@21))
)))
(assert (forall ((f@@1 T@U) (i@@5 Int) ) (!  (=> (= (type f@@1) (FieldType BoxType)) (= (FDim (MultiIndexField f@@1 i@@5)) (+ (FDim f@@1) 1)))
 :qid |DafnyPre.449:15|
 :skolemid |406|
 :pattern ( (MultiIndexField f@@1 i@@5))
)))
(assert (forall ((arg0@@66 T@U) ) (! (let ((T@@3 (FieldTypeInv0 (type arg0@@66))))
(= (type (MultiIndexField_Inverse0 arg0@@66)) (FieldType T@@3)))
 :qid |funType:MultiIndexField_Inverse0|
 :pattern ( (MultiIndexField_Inverse0 arg0@@66))
)))
(assert (forall ((f@@2 T@U) (i@@6 Int) ) (!  (=> (= (type f@@2) (FieldType BoxType)) (and (= (MultiIndexField_Inverse0 (MultiIndexField f@@2 i@@6)) f@@2) (= (MultiIndexField_Inverse1 (MultiIndexField f@@2 i@@6)) i@@6)))
 :qid |DafnyPre.452:15|
 :skolemid |407|
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
 :skolemid |408|
 :pattern ( (FieldOfDecl T@@4 cl nm))
)))
(assert (forall ((h@@11 T@U) (k T@U) (v@@24 T@U) (t@@21 T@U) ) (!  (=> (and (and (and (and (= (type h@@11) (MapType0Type refType MapType1Type)) (= (type k) (MapType0Type refType MapType1Type))) (= (type t@@21) TyType)) ($HeapSucc h@@11 k)) ($IsAlloc v@@24 t@@21 h@@11)) ($IsAlloc v@@24 t@@21 k))
 :qid |DafnyPre.474:17|
 :skolemid |409|
 :pattern ( ($HeapSucc h@@11 k) ($IsAlloc v@@24 t@@21 h@@11))
)))
(assert (forall ((h@@12 T@U) (k@@0 T@U) (bx@@30 T@U) (t@@22 T@U) ) (!  (=> (and (and (and (and (and (= (type h@@12) (MapType0Type refType MapType1Type)) (= (type k@@0) (MapType0Type refType MapType1Type))) (= (type bx@@30) BoxType)) (= (type t@@22) TyType)) ($HeapSucc h@@12 k@@0)) ($IsAllocBox bx@@30 t@@22 h@@12)) ($IsAllocBox bx@@30 t@@22 k@@0))
 :qid |DafnyPre.477:14|
 :skolemid |410|
 :pattern ( ($HeapSucc h@@12 k@@0) ($IsAllocBox bx@@30 t@@22 h@@12))
)))
(assert (= (FDim alloc) 0))
(assert (= (DeclName alloc) allocName))
(assert  (not ($IsGhostField alloc)))
(assert (forall ((o@@14 T@U) ) (!  (=> (= (type o@@14) refType) (<= 0 (_System.array.Length o@@14)))
 :qid |DafnyPre.494:15|
 :skolemid |411|
 :no-pattern (type o@@14)
 :no-pattern (U_2_int o@@14)
 :no-pattern (U_2_bool o@@14)
)))
(assert (forall ((x@@14 Real) ) (! (= (q@Int x@@14) (to_int x@@14))
 :qid |DafnyPre.500:14|
 :skolemid |412|
 :pattern ( (q@Int x@@14))
)))
(assert (forall ((x@@15 Int) ) (! (= (q@Real x@@15) (to_real x@@15))
 :qid |DafnyPre.501:15|
 :skolemid |413|
 :pattern ( (q@Real x@@15))
)))
(assert (forall ((i@@7 Int) ) (! (= (q@Int (q@Real i@@7)) i@@7)
 :qid |DafnyPre.502:15|
 :skolemid |414|
 :pattern ( (q@Int (q@Real i@@7)))
)))
(assert (= (type $OneHeap) (MapType0Type refType MapType1Type)))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((h@@13 T@U) (r@@0 T@U) (f@@3 T@U) (x@@16 T@U) ) (! (let ((alpha@@4 (type x@@16)))
 (=> (and (and (and (= (type h@@13) (MapType0Type refType MapType1Type)) (= (type r@@0) refType)) (= (type f@@3) (FieldType alpha@@4))) ($IsGoodHeap (MapType0Store h@@13 r@@0 (MapType1Store (MapType0Select h@@13 r@@0) f@@3 x@@16)))) ($HeapSucc h@@13 (MapType0Store h@@13 r@@0 (MapType1Store (MapType0Select h@@13 r@@0) f@@3 x@@16)))))
 :qid |DafnyPre.524:22|
 :skolemid |415|
 :pattern ( (MapType0Store h@@13 r@@0 (MapType1Store (MapType0Select h@@13 r@@0) f@@3 x@@16)))
)))
(assert (forall ((a@@2 T@U) (b@@2 T@U) (c T@U) ) (!  (=> (and (and (and (and (= (type a@@2) (MapType0Type refType MapType1Type)) (= (type b@@2) (MapType0Type refType MapType1Type))) (= (type c) (MapType0Type refType MapType1Type))) (not (= a@@2 c))) (and ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))) ($HeapSucc a@@2 c))
 :qid |DafnyPre.527:15|
 :skolemid |416|
 :pattern ( ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))
)))
(assert (forall ((h@@14 T@U) (k@@1 T@U) ) (!  (=> (and (and (= (type h@@14) (MapType0Type refType MapType1Type)) (= (type k@@1) (MapType0Type refType MapType1Type))) ($HeapSucc h@@14 k@@1)) (forall ((o@@15 T@U) ) (!  (=> (and (= (type o@@15) refType) (U_2_bool (MapType1Select (MapType0Select h@@14 o@@15) alloc))) (U_2_bool (MapType1Select (MapType0Select k@@1 o@@15) alloc)))
 :qid |DafnyPre.530:30|
 :skolemid |417|
 :pattern ( (MapType1Select (MapType0Select k@@1 o@@15) alloc))
)))
 :qid |DafnyPre.529:15|
 :skolemid |418|
 :pattern ( ($HeapSucc h@@14 k@@1))
)))
(assert (forall ((h@@15 T@U) (k@@2 T@U) ) (!  (=> (and (and (= (type h@@15) (MapType0Type refType MapType1Type)) (= (type k@@2) (MapType0Type refType MapType1Type))) ($HeapSuccGhost h@@15 k@@2)) (and ($HeapSucc h@@15 k@@2) (forall ((o@@16 T@U) (f@@4 T@U) ) (! (let ((alpha@@5 (FieldTypeInv0 (type f@@4))))
 (=> (and (and (= (type o@@16) refType) (= (type f@@4) (FieldType alpha@@5))) (not ($IsGhostField f@@4))) (= (MapType1Select (MapType0Select h@@15 o@@16) f@@4) (MapType1Select (MapType0Select k@@2 o@@16) f@@4))))
 :qid |DafnyPre.536:20|
 :skolemid |419|
 :pattern ( (MapType1Select (MapType0Select k@@2 o@@16) f@@4))
))))
 :qid |DafnyPre.533:15|
 :skolemid |420|
 :pattern ( ($HeapSuccGhost h@@15 k@@2))
)))
(assert (forall ((s@@3 T@U) ) (! (let ((T@@5 (MapType0TypeInv0 (type s@@3))))
 (=> (= (type s@@3) (MapType0Type T@@5 boolType)) (<= 0 (|Set#Card| s@@3))))
 :qid |DafnyPre.594:18|
 :skolemid |425|
 :pattern ( (|Set#Card| s@@3))
)))
(assert (forall ((T@@6 T@T) ) (! (= (type (|Set#Empty| T@@6)) (MapType0Type T@@6 boolType))
 :qid |funType:Set#Empty|
 :pattern ( (|Set#Empty| T@@6))
)))
(assert (forall ((o@@17 T@U) ) (! (let ((T@@7 (type o@@17)))
 (not (U_2_bool (MapType0Select (|Set#Empty| T@@7) o@@17))))
 :qid |DafnyPre.597:18|
 :skolemid |426|
 :pattern ( (let ((T@@7 (type o@@17)))
(MapType0Select (|Set#Empty| T@@7) o@@17)))
)))
(assert (forall ((s@@4 T@U) ) (! (let ((T@@8 (MapType0TypeInv0 (type s@@4))))
 (=> (= (type s@@4) (MapType0Type T@@8 boolType)) (and (and (=> (= (|Set#Card| s@@4) 0) (= s@@4 (|Set#Empty| T@@8))) (=> (= s@@4 (|Set#Empty| T@@8)) (= (|Set#Card| s@@4) 0))) (=> (not (= (|Set#Card| s@@4) 0)) (exists ((x@@17 T@U) ) (!  (and (= (type x@@17) T@@8) (U_2_bool (MapType0Select s@@4 x@@17)))
 :qid |DafnyPre.600:33|
 :skolemid |427|
 :no-pattern (type x@@17)
 :no-pattern (U_2_int x@@17)
 :no-pattern (U_2_bool x@@17)
))))))
 :qid |DafnyPre.598:18|
 :skolemid |428|
 :pattern ( (|Set#Card| s@@4))
)))
(assert (forall ((arg0@@70 T@U) ) (! (let ((T@@9 (type arg0@@70)))
(= (type (|Set#Singleton| arg0@@70)) (MapType0Type T@@9 boolType)))
 :qid |funType:Set#Singleton|
 :pattern ( (|Set#Singleton| arg0@@70))
)))
(assert (forall ((r@@1 T@U) ) (! (U_2_bool (MapType0Select (|Set#Singleton| r@@1) r@@1))
 :qid |DafnyPre.606:18|
 :skolemid |429|
 :pattern ( (|Set#Singleton| r@@1))
)))
(assert (forall ((r@@2 T@U) (o@@18 T@U) ) (! (let ((T@@10 (type r@@2)))
 (=> (= (type o@@18) T@@10) (and (=> (U_2_bool (MapType0Select (|Set#Singleton| r@@2) o@@18)) (= r@@2 o@@18)) (=> (= r@@2 o@@18) (U_2_bool (MapType0Select (|Set#Singleton| r@@2) o@@18))))))
 :qid |DafnyPre.607:18|
 :skolemid |430|
 :pattern ( (MapType0Select (|Set#Singleton| r@@2) o@@18))
)))
(assert (forall ((r@@3 T@U) ) (! (= (|Set#Card| (|Set#Singleton| r@@3)) 1)
 :qid |DafnyPre.608:18|
 :skolemid |431|
 :pattern ( (|Set#Card| (|Set#Singleton| r@@3)))
)))
(assert (forall ((arg0@@71 T@U) (arg1@@23 T@U) ) (! (let ((T@@11 (type arg1@@23)))
(= (type (|Set#UnionOne| arg0@@71 arg1@@23)) (MapType0Type T@@11 boolType)))
 :qid |funType:Set#UnionOne|
 :pattern ( (|Set#UnionOne| arg0@@71 arg1@@23))
)))
(assert (forall ((a@@3 T@U) (x@@18 T@U) (o@@19 T@U) ) (! (let ((T@@12 (type x@@18)))
 (=> (and (= (type a@@3) (MapType0Type T@@12 boolType)) (= (type o@@19) T@@12)) (and (=> (U_2_bool (MapType0Select (|Set#UnionOne| a@@3 x@@18) o@@19)) (or (= o@@19 x@@18) (U_2_bool (MapType0Select a@@3 o@@19)))) (=> (or (= o@@19 x@@18) (U_2_bool (MapType0Select a@@3 o@@19))) (U_2_bool (MapType0Select (|Set#UnionOne| a@@3 x@@18) o@@19))))))
 :qid |DafnyPre.611:18|
 :skolemid |432|
 :pattern ( (MapType0Select (|Set#UnionOne| a@@3 x@@18) o@@19))
)))
(assert (forall ((a@@4 T@U) (x@@19 T@U) ) (! (let ((T@@13 (type x@@19)))
 (=> (= (type a@@4) (MapType0Type T@@13 boolType)) (U_2_bool (MapType0Select (|Set#UnionOne| a@@4 x@@19) x@@19))))
 :qid |DafnyPre.613:18|
 :skolemid |433|
 :pattern ( (|Set#UnionOne| a@@4 x@@19))
)))
(assert (forall ((a@@5 T@U) (x@@20 T@U) (y@@1 T@U) ) (! (let ((T@@14 (type x@@20)))
 (=> (and (and (= (type a@@5) (MapType0Type T@@14 boolType)) (= (type y@@1) T@@14)) (U_2_bool (MapType0Select a@@5 y@@1))) (U_2_bool (MapType0Select (|Set#UnionOne| a@@5 x@@20) y@@1))))
 :qid |DafnyPre.615:18|
 :skolemid |434|
 :pattern ( (|Set#UnionOne| a@@5 x@@20) (MapType0Select a@@5 y@@1))
)))
(assert (forall ((a@@6 T@U) (x@@21 T@U) ) (! (let ((T@@15 (type x@@21)))
 (=> (and (= (type a@@6) (MapType0Type T@@15 boolType)) (U_2_bool (MapType0Select a@@6 x@@21))) (= (|Set#Card| (|Set#UnionOne| a@@6 x@@21)) (|Set#Card| a@@6))))
 :qid |DafnyPre.617:18|
 :skolemid |435|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@6 x@@21)))
)))
(assert (forall ((a@@7 T@U) (x@@22 T@U) ) (! (let ((T@@16 (type x@@22)))
 (=> (and (= (type a@@7) (MapType0Type T@@16 boolType)) (not (U_2_bool (MapType0Select a@@7 x@@22)))) (= (|Set#Card| (|Set#UnionOne| a@@7 x@@22)) (+ (|Set#Card| a@@7) 1))))
 :qid |DafnyPre.619:18|
 :skolemid |436|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@7 x@@22)))
)))
(assert (forall ((arg0@@72 T@U) (arg1@@24 T@U) ) (! (let ((T@@17 (MapType0TypeInv0 (type arg0@@72))))
(= (type (|Set#Union| arg0@@72 arg1@@24)) (MapType0Type T@@17 boolType)))
 :qid |funType:Set#Union|
 :pattern ( (|Set#Union| arg0@@72 arg1@@24))
)))
(assert (forall ((a@@8 T@U) (b@@3 T@U) (o@@20 T@U) ) (! (let ((T@@18 (type o@@20)))
 (=> (and (= (type a@@8) (MapType0Type T@@18 boolType)) (= (type b@@3) (MapType0Type T@@18 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Union| a@@8 b@@3) o@@20)) (or (U_2_bool (MapType0Select a@@8 o@@20)) (U_2_bool (MapType0Select b@@3 o@@20)))) (=> (or (U_2_bool (MapType0Select a@@8 o@@20)) (U_2_bool (MapType0Select b@@3 o@@20))) (U_2_bool (MapType0Select (|Set#Union| a@@8 b@@3) o@@20))))))
 :qid |DafnyPre.623:18|
 :skolemid |437|
 :pattern ( (MapType0Select (|Set#Union| a@@8 b@@3) o@@20))
)))
(assert (forall ((a@@9 T@U) (b@@4 T@U) (y@@2 T@U) ) (! (let ((T@@19 (type y@@2)))
 (=> (and (and (= (type a@@9) (MapType0Type T@@19 boolType)) (= (type b@@4) (MapType0Type T@@19 boolType))) (U_2_bool (MapType0Select a@@9 y@@2))) (U_2_bool (MapType0Select (|Set#Union| a@@9 b@@4) y@@2))))
 :qid |DafnyPre.625:18|
 :skolemid |438|
 :pattern ( (|Set#Union| a@@9 b@@4) (MapType0Select a@@9 y@@2))
)))
(assert (forall ((a@@10 T@U) (b@@5 T@U) (y@@3 T@U) ) (! (let ((T@@20 (type y@@3)))
 (=> (and (and (= (type a@@10) (MapType0Type T@@20 boolType)) (= (type b@@5) (MapType0Type T@@20 boolType))) (U_2_bool (MapType0Select b@@5 y@@3))) (U_2_bool (MapType0Select (|Set#Union| a@@10 b@@5) y@@3))))
 :qid |DafnyPre.627:18|
 :skolemid |439|
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
 :skolemid |440|
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
 :skolemid |441|
 :pattern ( (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@21))
)))
(assert (forall ((a@@13 T@U) (b@@8 T@U) ) (! (let ((T@@25 (MapType0TypeInv0 (type a@@13))))
 (=> (and (= (type a@@13) (MapType0Type T@@25 boolType)) (= (type b@@8) (MapType0Type T@@25 boolType))) (= (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8) (|Set#Union| a@@13 b@@8))))
 :qid |DafnyPre.642:18|
 :skolemid |442|
 :pattern ( (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8))
)))
(assert (forall ((a@@14 T@U) (b@@9 T@U) ) (! (let ((T@@26 (MapType0TypeInv0 (type a@@14))))
 (=> (and (= (type a@@14) (MapType0Type T@@26 boolType)) (= (type b@@9) (MapType0Type T@@26 boolType))) (= (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)) (|Set#Union| a@@14 b@@9))))
 :qid |DafnyPre.644:18|
 :skolemid |443|
 :pattern ( (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)))
)))
(assert (forall ((a@@15 T@U) (b@@10 T@U) ) (! (let ((T@@27 (MapType0TypeInv0 (type a@@15))))
 (=> (and (= (type a@@15) (MapType0Type T@@27 boolType)) (= (type b@@10) (MapType0Type T@@27 boolType))) (= (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10) (|Set#Intersection| a@@15 b@@10))))
 :qid |DafnyPre.646:18|
 :skolemid |444|
 :pattern ( (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10))
)))
(assert (forall ((a@@16 T@U) (b@@11 T@U) ) (! (let ((T@@28 (MapType0TypeInv0 (type a@@16))))
 (=> (and (= (type a@@16) (MapType0Type T@@28 boolType)) (= (type b@@11) (MapType0Type T@@28 boolType))) (= (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)) (|Set#Intersection| a@@16 b@@11))))
 :qid |DafnyPre.648:18|
 :skolemid |445|
 :pattern ( (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)))
)))
(assert (forall ((a@@17 T@U) (b@@12 T@U) ) (! (let ((T@@29 (MapType0TypeInv0 (type a@@17))))
 (=> (and (= (type a@@17) (MapType0Type T@@29 boolType)) (= (type b@@12) (MapType0Type T@@29 boolType))) (= (+ (|Set#Card| (|Set#Union| a@@17 b@@12)) (|Set#Card| (|Set#Intersection| a@@17 b@@12))) (+ (|Set#Card| a@@17) (|Set#Card| b@@12)))))
 :qid |DafnyPre.650:18|
 :skolemid |446|
 :pattern ( (|Set#Card| (|Set#Union| a@@17 b@@12)))
 :pattern ( (|Set#Card| (|Set#Intersection| a@@17 b@@12)))
)))
(assert (forall ((a@@18 T@U) (b@@13 T@U) (o@@22 T@U) ) (! (let ((T@@30 (type o@@22)))
 (=> (and (= (type a@@18) (MapType0Type T@@30 boolType)) (= (type b@@13) (MapType0Type T@@30 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22)) (and (U_2_bool (MapType0Select a@@18 o@@22)) (not (U_2_bool (MapType0Select b@@13 o@@22))))) (=> (and (U_2_bool (MapType0Select a@@18 o@@22)) (not (U_2_bool (MapType0Select b@@13 o@@22)))) (U_2_bool (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22))))))
 :qid |DafnyPre.654:18|
 :skolemid |447|
 :pattern ( (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22))
)))
(assert (forall ((a@@19 T@U) (b@@14 T@U) (y@@4 T@U) ) (! (let ((T@@31 (type y@@4)))
 (=> (and (and (= (type a@@19) (MapType0Type T@@31 boolType)) (= (type b@@14) (MapType0Type T@@31 boolType))) (U_2_bool (MapType0Select b@@14 y@@4))) (not (U_2_bool (MapType0Select (|Set#Difference| a@@19 b@@14) y@@4)))))
 :qid |DafnyPre.656:18|
 :skolemid |448|
 :pattern ( (|Set#Difference| a@@19 b@@14) (MapType0Select b@@14 y@@4))
)))
(assert (forall ((a@@20 T@U) (b@@15 T@U) ) (! (let ((T@@32 (MapType0TypeInv0 (type a@@20))))
 (=> (and (= (type a@@20) (MapType0Type T@@32 boolType)) (= (type b@@15) (MapType0Type T@@32 boolType))) (and (= (+ (+ (|Set#Card| (|Set#Difference| a@@20 b@@15)) (|Set#Card| (|Set#Difference| b@@15 a@@20))) (|Set#Card| (|Set#Intersection| a@@20 b@@15))) (|Set#Card| (|Set#Union| a@@20 b@@15))) (= (|Set#Card| (|Set#Difference| a@@20 b@@15)) (- (|Set#Card| a@@20) (|Set#Card| (|Set#Intersection| a@@20 b@@15)))))))
 :qid |DafnyPre.658:18|
 :skolemid |449|
 :pattern ( (|Set#Card| (|Set#Difference| a@@20 b@@15)))
)))
(assert (forall ((a@@21 T@U) (b@@16 T@U) ) (! (let ((T@@33 (MapType0TypeInv0 (type a@@21))))
 (=> (and (= (type a@@21) (MapType0Type T@@33 boolType)) (= (type b@@16) (MapType0Type T@@33 boolType))) (and (=> (|Set#Subset| a@@21 b@@16) (forall ((o@@23 T@U) ) (!  (=> (and (= (type o@@23) T@@33) (U_2_bool (MapType0Select a@@21 o@@23))) (U_2_bool (MapType0Select b@@16 o@@23)))
 :qid |DafnyPre.667:32|
 :skolemid |450|
 :pattern ( (MapType0Select a@@21 o@@23))
 :pattern ( (MapType0Select b@@16 o@@23))
))) (=> (forall ((o@@24 T@U) ) (!  (=> (and (= (type o@@24) T@@33) (U_2_bool (MapType0Select a@@21 o@@24))) (U_2_bool (MapType0Select b@@16 o@@24)))
 :qid |DafnyPre.667:32|
 :skolemid |450|
 :pattern ( (MapType0Select a@@21 o@@24))
 :pattern ( (MapType0Select b@@16 o@@24))
)) (|Set#Subset| a@@21 b@@16)))))
 :qid |DafnyPre.666:17|
 :skolemid |451|
 :pattern ( (|Set#Subset| a@@21 b@@16))
)))
(assert (forall ((a@@22 T@U) (b@@17 T@U) ) (! (let ((T@@34 (MapType0TypeInv0 (type a@@22))))
 (=> (and (= (type a@@22) (MapType0Type T@@34 boolType)) (= (type b@@17) (MapType0Type T@@34 boolType))) (and (=> (|Set#Equal| a@@22 b@@17) (forall ((o@@25 T@U) ) (!  (=> (= (type o@@25) T@@34) (and (=> (U_2_bool (MapType0Select a@@22 o@@25)) (U_2_bool (MapType0Select b@@17 o@@25))) (=> (U_2_bool (MapType0Select b@@17 o@@25)) (U_2_bool (MapType0Select a@@22 o@@25)))))
 :qid |DafnyPre.675:31|
 :skolemid |452|
 :pattern ( (MapType0Select a@@22 o@@25))
 :pattern ( (MapType0Select b@@17 o@@25))
))) (=> (forall ((o@@26 T@U) ) (!  (=> (= (type o@@26) T@@34) (and (=> (U_2_bool (MapType0Select a@@22 o@@26)) (U_2_bool (MapType0Select b@@17 o@@26))) (=> (U_2_bool (MapType0Select b@@17 o@@26)) (U_2_bool (MapType0Select a@@22 o@@26)))))
 :qid |DafnyPre.675:31|
 :skolemid |452|
 :pattern ( (MapType0Select a@@22 o@@26))
 :pattern ( (MapType0Select b@@17 o@@26))
)) (|Set#Equal| a@@22 b@@17)))))
 :qid |DafnyPre.674:17|
 :skolemid |453|
 :pattern ( (|Set#Equal| a@@22 b@@17))
)))
(assert (forall ((a@@23 T@U) (b@@18 T@U) ) (! (let ((T@@35 (MapType0TypeInv0 (type a@@23))))
 (=> (and (and (= (type a@@23) (MapType0Type T@@35 boolType)) (= (type b@@18) (MapType0Type T@@35 boolType))) (|Set#Equal| a@@23 b@@18)) (= a@@23 b@@18)))
 :qid |DafnyPre.676:17|
 :skolemid |454|
 :pattern ( (|Set#Equal| a@@23 b@@18))
)))
(assert (forall ((a@@24 T@U) (b@@19 T@U) ) (! (let ((T@@36 (MapType0TypeInv0 (type a@@24))))
 (=> (and (= (type a@@24) (MapType0Type T@@36 boolType)) (= (type b@@19) (MapType0Type T@@36 boolType))) (and (=> (|Set#Disjoint| a@@24 b@@19) (forall ((o@@27 T@U) ) (!  (=> (= (type o@@27) T@@36) (or (not (U_2_bool (MapType0Select a@@24 o@@27))) (not (U_2_bool (MapType0Select b@@19 o@@27)))))
 :qid |DafnyPre.681:34|
 :skolemid |455|
 :pattern ( (MapType0Select a@@24 o@@27))
 :pattern ( (MapType0Select b@@19 o@@27))
))) (=> (forall ((o@@28 T@U) ) (!  (=> (= (type o@@28) T@@36) (or (not (U_2_bool (MapType0Select a@@24 o@@28))) (not (U_2_bool (MapType0Select b@@19 o@@28)))))
 :qid |DafnyPre.681:34|
 :skolemid |455|
 :pattern ( (MapType0Select a@@24 o@@28))
 :pattern ( (MapType0Select b@@19 o@@28))
)) (|Set#Disjoint| a@@24 b@@19)))))
 :qid |DafnyPre.680:18|
 :skolemid |456|
 :pattern ( (|Set#Disjoint| a@@24 b@@19))
)))
(assert (forall ((T@@37 T@T) ) (! (= (type (|ISet#Empty| T@@37)) (MapType0Type T@@37 boolType))
 :qid |funType:ISet#Empty|
 :pattern ( (|ISet#Empty| T@@37))
)))
(assert (forall ((o@@29 T@U) ) (! (let ((T@@38 (type o@@29)))
 (not (U_2_bool (MapType0Select (|ISet#Empty| T@@38) o@@29))))
 :qid |DafnyPre.690:18|
 :skolemid |457|
 :pattern ( (let ((T@@38 (type o@@29)))
(MapType0Select (|ISet#Empty| T@@38) o@@29)))
)))
(assert (forall ((arg0@@75 T@U) (arg1@@27 T@U) ) (! (let ((T@@39 (type arg1@@27)))
(= (type (|ISet#UnionOne| arg0@@75 arg1@@27)) (MapType0Type T@@39 boolType)))
 :qid |funType:ISet#UnionOne|
 :pattern ( (|ISet#UnionOne| arg0@@75 arg1@@27))
)))
(assert (forall ((a@@25 T@U) (x@@23 T@U) (o@@30 T@U) ) (! (let ((T@@40 (type x@@23)))
 (=> (and (= (type a@@25) (MapType0Type T@@40 boolType)) (= (type o@@30) T@@40)) (and (=> (U_2_bool (MapType0Select (|ISet#UnionOne| a@@25 x@@23) o@@30)) (or (= o@@30 x@@23) (U_2_bool (MapType0Select a@@25 o@@30)))) (=> (or (= o@@30 x@@23) (U_2_bool (MapType0Select a@@25 o@@30))) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@25 x@@23) o@@30))))))
 :qid |DafnyPre.697:18|
 :skolemid |458|
 :pattern ( (MapType0Select (|ISet#UnionOne| a@@25 x@@23) o@@30))
)))
(assert (forall ((a@@26 T@U) (x@@24 T@U) ) (! (let ((T@@41 (type x@@24)))
 (=> (= (type a@@26) (MapType0Type T@@41 boolType)) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@26 x@@24) x@@24))))
 :qid |DafnyPre.699:18|
 :skolemid |459|
 :pattern ( (|ISet#UnionOne| a@@26 x@@24))
)))
(assert (forall ((a@@27 T@U) (x@@25 T@U) (y@@5 T@U) ) (! (let ((T@@42 (type x@@25)))
 (=> (and (and (= (type a@@27) (MapType0Type T@@42 boolType)) (= (type y@@5) T@@42)) (U_2_bool (MapType0Select a@@27 y@@5))) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@27 x@@25) y@@5))))
 :qid |DafnyPre.701:18|
 :skolemid |460|
 :pattern ( (|ISet#UnionOne| a@@27 x@@25) (MapType0Select a@@27 y@@5))
)))
(assert (forall ((arg0@@76 T@U) (arg1@@28 T@U) ) (! (let ((T@@43 (MapType0TypeInv0 (type arg0@@76))))
(= (type (|ISet#Union| arg0@@76 arg1@@28)) (MapType0Type T@@43 boolType)))
 :qid |funType:ISet#Union|
 :pattern ( (|ISet#Union| arg0@@76 arg1@@28))
)))
(assert (forall ((a@@28 T@U) (b@@20 T@U) (o@@31 T@U) ) (! (let ((T@@44 (type o@@31)))
 (=> (and (= (type a@@28) (MapType0Type T@@44 boolType)) (= (type b@@20) (MapType0Type T@@44 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Union| a@@28 b@@20) o@@31)) (or (U_2_bool (MapType0Select a@@28 o@@31)) (U_2_bool (MapType0Select b@@20 o@@31)))) (=> (or (U_2_bool (MapType0Select a@@28 o@@31)) (U_2_bool (MapType0Select b@@20 o@@31))) (U_2_bool (MapType0Select (|ISet#Union| a@@28 b@@20) o@@31))))))
 :qid |DafnyPre.705:18|
 :skolemid |461|
 :pattern ( (MapType0Select (|ISet#Union| a@@28 b@@20) o@@31))
)))
(assert (forall ((a@@29 T@U) (b@@21 T@U) (y@@6 T@U) ) (! (let ((T@@45 (type y@@6)))
 (=> (and (and (= (type a@@29) (MapType0Type T@@45 boolType)) (= (type b@@21) (MapType0Type T@@45 boolType))) (U_2_bool (MapType0Select a@@29 y@@6))) (U_2_bool (MapType0Select (|ISet#Union| a@@29 b@@21) y@@6))))
 :qid |DafnyPre.707:18|
 :skolemid |462|
 :pattern ( (|ISet#Union| a@@29 b@@21) (MapType0Select a@@29 y@@6))
)))
(assert (forall ((a@@30 T@U) (b@@22 T@U) (y@@7 T@U) ) (! (let ((T@@46 (type y@@7)))
 (=> (and (and (= (type a@@30) (MapType0Type T@@46 boolType)) (= (type b@@22) (MapType0Type T@@46 boolType))) (U_2_bool (MapType0Select b@@22 y@@7))) (U_2_bool (MapType0Select (|ISet#Union| a@@30 b@@22) y@@7))))
 :qid |DafnyPre.709:18|
 :skolemid |463|
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
 :skolemid |464|
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
 :skolemid |465|
 :pattern ( (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@32))
)))
(assert (forall ((a@@33 T@U) (b@@25 T@U) ) (! (let ((T@@51 (MapType0TypeInv0 (type a@@33))))
 (=> (and (= (type a@@33) (MapType0Type T@@51 boolType)) (= (type b@@25) (MapType0Type T@@51 boolType))) (= (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25) (|ISet#Union| a@@33 b@@25))))
 :qid |DafnyPre.724:18|
 :skolemid |466|
 :pattern ( (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25))
)))
(assert (forall ((a@@34 T@U) (b@@26 T@U) ) (! (let ((T@@52 (MapType0TypeInv0 (type a@@34))))
 (=> (and (= (type a@@34) (MapType0Type T@@52 boolType)) (= (type b@@26) (MapType0Type T@@52 boolType))) (= (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)) (|ISet#Union| a@@34 b@@26))))
 :qid |DafnyPre.726:18|
 :skolemid |467|
 :pattern ( (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)))
)))
(assert (forall ((a@@35 T@U) (b@@27 T@U) ) (! (let ((T@@53 (MapType0TypeInv0 (type a@@35))))
 (=> (and (= (type a@@35) (MapType0Type T@@53 boolType)) (= (type b@@27) (MapType0Type T@@53 boolType))) (= (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27) (|ISet#Intersection| a@@35 b@@27))))
 :qid |DafnyPre.728:18|
 :skolemid |468|
 :pattern ( (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27))
)))
(assert (forall ((a@@36 T@U) (b@@28 T@U) ) (! (let ((T@@54 (MapType0TypeInv0 (type a@@36))))
 (=> (and (= (type a@@36) (MapType0Type T@@54 boolType)) (= (type b@@28) (MapType0Type T@@54 boolType))) (= (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)) (|ISet#Intersection| a@@36 b@@28))))
 :qid |DafnyPre.730:18|
 :skolemid |469|
 :pattern ( (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)))
)))
(assert (forall ((a@@37 T@U) (b@@29 T@U) (o@@33 T@U) ) (! (let ((T@@55 (type o@@33)))
 (=> (and (= (type a@@37) (MapType0Type T@@55 boolType)) (= (type b@@29) (MapType0Type T@@55 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@33)) (and (U_2_bool (MapType0Select a@@37 o@@33)) (not (U_2_bool (MapType0Select b@@29 o@@33))))) (=> (and (U_2_bool (MapType0Select a@@37 o@@33)) (not (U_2_bool (MapType0Select b@@29 o@@33)))) (U_2_bool (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@33))))))
 :qid |DafnyPre.735:18|
 :skolemid |470|
 :pattern ( (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@33))
)))
(assert (forall ((a@@38 T@U) (b@@30 T@U) (y@@8 T@U) ) (! (let ((T@@56 (type y@@8)))
 (=> (and (and (= (type a@@38) (MapType0Type T@@56 boolType)) (= (type b@@30) (MapType0Type T@@56 boolType))) (U_2_bool (MapType0Select b@@30 y@@8))) (not (U_2_bool (MapType0Select (|ISet#Difference| a@@38 b@@30) y@@8)))))
 :qid |DafnyPre.737:18|
 :skolemid |471|
 :pattern ( (|ISet#Difference| a@@38 b@@30) (MapType0Select b@@30 y@@8))
)))
(assert (forall ((a@@39 T@U) (b@@31 T@U) ) (! (let ((T@@57 (MapType0TypeInv0 (type a@@39))))
 (=> (and (= (type a@@39) (MapType0Type T@@57 boolType)) (= (type b@@31) (MapType0Type T@@57 boolType))) (and (=> (|ISet#Subset| a@@39 b@@31) (forall ((o@@34 T@U) ) (!  (=> (and (= (type o@@34) T@@57) (U_2_bool (MapType0Select a@@39 o@@34))) (U_2_bool (MapType0Select b@@31 o@@34)))
 :qid |DafnyPre.742:33|
 :skolemid |472|
 :pattern ( (MapType0Select a@@39 o@@34))
 :pattern ( (MapType0Select b@@31 o@@34))
))) (=> (forall ((o@@35 T@U) ) (!  (=> (and (= (type o@@35) T@@57) (U_2_bool (MapType0Select a@@39 o@@35))) (U_2_bool (MapType0Select b@@31 o@@35)))
 :qid |DafnyPre.742:33|
 :skolemid |472|
 :pattern ( (MapType0Select a@@39 o@@35))
 :pattern ( (MapType0Select b@@31 o@@35))
)) (|ISet#Subset| a@@39 b@@31)))))
 :qid |DafnyPre.741:17|
 :skolemid |473|
 :pattern ( (|ISet#Subset| a@@39 b@@31))
)))
(assert (forall ((a@@40 T@U) (b@@32 T@U) ) (! (let ((T@@58 (MapType0TypeInv0 (type a@@40))))
 (=> (and (= (type a@@40) (MapType0Type T@@58 boolType)) (= (type b@@32) (MapType0Type T@@58 boolType))) (and (=> (|ISet#Equal| a@@40 b@@32) (forall ((o@@36 T@U) ) (!  (=> (= (type o@@36) T@@58) (and (=> (U_2_bool (MapType0Select a@@40 o@@36)) (U_2_bool (MapType0Select b@@32 o@@36))) (=> (U_2_bool (MapType0Select b@@32 o@@36)) (U_2_bool (MapType0Select a@@40 o@@36)))))
 :qid |DafnyPre.750:32|
 :skolemid |474|
 :pattern ( (MapType0Select a@@40 o@@36))
 :pattern ( (MapType0Select b@@32 o@@36))
))) (=> (forall ((o@@37 T@U) ) (!  (=> (= (type o@@37) T@@58) (and (=> (U_2_bool (MapType0Select a@@40 o@@37)) (U_2_bool (MapType0Select b@@32 o@@37))) (=> (U_2_bool (MapType0Select b@@32 o@@37)) (U_2_bool (MapType0Select a@@40 o@@37)))))
 :qid |DafnyPre.750:32|
 :skolemid |474|
 :pattern ( (MapType0Select a@@40 o@@37))
 :pattern ( (MapType0Select b@@32 o@@37))
)) (|ISet#Equal| a@@40 b@@32)))))
 :qid |DafnyPre.749:17|
 :skolemid |475|
 :pattern ( (|ISet#Equal| a@@40 b@@32))
)))
(assert (forall ((a@@41 T@U) (b@@33 T@U) ) (! (let ((T@@59 (MapType0TypeInv0 (type a@@41))))
 (=> (and (and (= (type a@@41) (MapType0Type T@@59 boolType)) (= (type b@@33) (MapType0Type T@@59 boolType))) (|ISet#Equal| a@@41 b@@33)) (= a@@41 b@@33)))
 :qid |DafnyPre.751:17|
 :skolemid |476|
 :pattern ( (|ISet#Equal| a@@41 b@@33))
)))
(assert (forall ((a@@42 T@U) (b@@34 T@U) ) (! (let ((T@@60 (MapType0TypeInv0 (type a@@42))))
 (=> (and (= (type a@@42) (MapType0Type T@@60 boolType)) (= (type b@@34) (MapType0Type T@@60 boolType))) (and (=> (|ISet#Disjoint| a@@42 b@@34) (forall ((o@@38 T@U) ) (!  (=> (= (type o@@38) T@@60) (or (not (U_2_bool (MapType0Select a@@42 o@@38))) (not (U_2_bool (MapType0Select b@@34 o@@38)))))
 :qid |DafnyPre.756:35|
 :skolemid |477|
 :pattern ( (MapType0Select a@@42 o@@38))
 :pattern ( (MapType0Select b@@34 o@@38))
))) (=> (forall ((o@@39 T@U) ) (!  (=> (= (type o@@39) T@@60) (or (not (U_2_bool (MapType0Select a@@42 o@@39))) (not (U_2_bool (MapType0Select b@@34 o@@39)))))
 :qid |DafnyPre.756:35|
 :skolemid |477|
 :pattern ( (MapType0Select a@@42 o@@39))
 :pattern ( (MapType0Select b@@34 o@@39))
)) (|ISet#Disjoint| a@@42 b@@34)))))
 :qid |DafnyPre.755:18|
 :skolemid |478|
 :pattern ( (|ISet#Disjoint| a@@42 b@@34))
)))
(assert (forall ((a@@43 Int) (b@@35 Int) ) (!  (and (=> (<= a@@43 b@@35) (= (|Math#min| a@@43 b@@35) a@@43)) (=> (= (|Math#min| a@@43 b@@35) a@@43) (<= a@@43 b@@35)))
 :qid |DafnyPre.763:15|
 :skolemid |479|
 :pattern ( (|Math#min| a@@43 b@@35))
)))
(assert (forall ((a@@44 Int) (b@@36 Int) ) (!  (and (=> (<= b@@36 a@@44) (= (|Math#min| a@@44 b@@36) b@@36)) (=> (= (|Math#min| a@@44 b@@36) b@@36) (<= b@@36 a@@44)))
 :qid |DafnyPre.764:15|
 :skolemid |480|
 :pattern ( (|Math#min| a@@44 b@@36))
)))
(assert (forall ((a@@45 Int) (b@@37 Int) ) (!  (or (= (|Math#min| a@@45 b@@37) a@@45) (= (|Math#min| a@@45 b@@37) b@@37))
 :qid |DafnyPre.765:15|
 :skolemid |481|
 :pattern ( (|Math#min| a@@45 b@@37))
)))
(assert (forall ((a@@46 Int) ) (!  (=> (<= 0 a@@46) (= (|Math#clip| a@@46) a@@46))
 :qid |DafnyPre.768:15|
 :skolemid |482|
 :pattern ( (|Math#clip| a@@46))
)))
(assert (forall ((a@@47 Int) ) (!  (=> (< a@@47 0) (= (|Math#clip| a@@47) 0))
 :qid |DafnyPre.769:15|
 :skolemid |483|
 :pattern ( (|Math#clip| a@@47))
)))
(assert (forall ((ms T@U) ) (! (let ((T@@61 (MapType0TypeInv0 (type ms))))
 (=> (= (type ms) (MapType0Type T@@61 intType)) (and (=> ($IsGoodMultiSet ms) (forall ((bx@@31 T@U) ) (!  (=> (= (type bx@@31) T@@61) (and (<= 0 (U_2_int (MapType0Select ms bx@@31))) (<= (U_2_int (MapType0Select ms bx@@31)) (|MultiSet#Card| ms))))
 :qid |DafnyPre.777:11|
 :skolemid |484|
 :pattern ( (MapType0Select ms bx@@31))
))) (=> (forall ((bx@@32 T@U) ) (!  (=> (= (type bx@@32) T@@61) (and (<= 0 (U_2_int (MapType0Select ms bx@@32))) (<= (U_2_int (MapType0Select ms bx@@32)) (|MultiSet#Card| ms))))
 :qid |DafnyPre.777:11|
 :skolemid |484|
 :pattern ( (MapType0Select ms bx@@32))
)) ($IsGoodMultiSet ms)))))
 :qid |DafnyPre.775:18|
 :skolemid |485|
 :pattern ( ($IsGoodMultiSet ms))
)))
(assert (forall ((s@@5 T@U) ) (! (let ((T@@62 (MapType0TypeInv0 (type s@@5))))
 (=> (= (type s@@5) (MapType0Type T@@62 intType)) (<= 0 (|MultiSet#Card| s@@5))))
 :qid |DafnyPre.780:18|
 :skolemid |486|
 :pattern ( (|MultiSet#Card| s@@5))
)))
(assert (forall ((s@@6 T@U) (x@@26 T@U) (n@@5 T@U) ) (! (let ((T@@63 (type x@@26)))
 (=> (and (and (= (type s@@6) (MapType0Type T@@63 intType)) (= (type n@@5) intType)) (<= 0 (U_2_int n@@5))) (= (|MultiSet#Card| (MapType0Store s@@6 x@@26 n@@5)) (+ (- (|MultiSet#Card| s@@6) (U_2_int (MapType0Select s@@6 x@@26))) (U_2_int n@@5)))))
 :qid |DafnyPre.781:18|
 :skolemid |487|
 :pattern ( (|MultiSet#Card| (MapType0Store s@@6 x@@26 n@@5)))
)))
(assert (forall ((T@@64 T@T) ) (! (= (type (|MultiSet#Empty| T@@64)) (MapType0Type T@@64 intType))
 :qid |funType:MultiSet#Empty|
 :pattern ( (|MultiSet#Empty| T@@64))
)))
(assert (forall ((o@@40 T@U) ) (! (let ((T@@65 (type o@@40)))
(= (U_2_int (MapType0Select (|MultiSet#Empty| T@@65) o@@40)) 0))
 :qid |DafnyPre.785:18|
 :skolemid |488|
 :pattern ( (let ((T@@65 (type o@@40)))
(MapType0Select (|MultiSet#Empty| T@@65) o@@40)))
)))
(assert (forall ((s@@7 T@U) ) (! (let ((T@@66 (MapType0TypeInv0 (type s@@7))))
 (=> (= (type s@@7) (MapType0Type T@@66 intType)) (and (and (=> (= (|MultiSet#Card| s@@7) 0) (= s@@7 (|MultiSet#Empty| T@@66))) (=> (= s@@7 (|MultiSet#Empty| T@@66)) (= (|MultiSet#Card| s@@7) 0))) (=> (not (= (|MultiSet#Card| s@@7) 0)) (exists ((x@@27 T@U) ) (!  (and (= (type x@@27) T@@66) (< 0 (U_2_int (MapType0Select s@@7 x@@27))))
 :qid |DafnyPre.788:38|
 :skolemid |489|
 :no-pattern (type x@@27)
 :no-pattern (U_2_int x@@27)
 :no-pattern (U_2_bool x@@27)
))))))
 :qid |DafnyPre.786:18|
 :skolemid |490|
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
 :skolemid |491|
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
 :skolemid |492|
 :pattern ( (|MultiSet#Singleton| r@@5))
)))
(assert (forall ((a@@48 T@U) (x@@28 T@U) (o@@42 T@U) ) (! (let ((T@@71 (type x@@28)))
 (=> (and (= (type a@@48) (MapType0Type T@@71 intType)) (= (type o@@42) T@@71)) (and (=> (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@48 x@@28) o@@42))) (or (= o@@42 x@@28) (< 0 (U_2_int (MapType0Select a@@48 o@@42))))) (=> (or (= o@@42 x@@28) (< 0 (U_2_int (MapType0Select a@@48 o@@42)))) (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@48 x@@28) o@@42)))))))
 :qid |DafnyPre.797:18|
 :skolemid |493|
 :pattern ( (MapType0Select (|MultiSet#UnionOne| a@@48 x@@28) o@@42))
)))
(assert (forall ((a@@49 T@U) (x@@29 T@U) ) (! (let ((T@@72 (type x@@29)))
 (=> (= (type a@@49) (MapType0Type T@@72 intType)) (= (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@49 x@@29) x@@29)) (+ (U_2_int (MapType0Select a@@49 x@@29)) 1))))
 :qid |DafnyPre.800:18|
 :skolemid |494|
 :pattern ( (|MultiSet#UnionOne| a@@49 x@@29))
)))
(assert (forall ((a@@50 T@U) (x@@30 T@U) (y@@9 T@U) ) (! (let ((T@@73 (type x@@30)))
 (=> (and (and (= (type a@@50) (MapType0Type T@@73 intType)) (= (type y@@9) T@@73)) (< 0 (U_2_int (MapType0Select a@@50 y@@9)))) (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@50 x@@30) y@@9)))))
 :qid |DafnyPre.803:18|
 :skolemid |495|
 :pattern ( (|MultiSet#UnionOne| a@@50 x@@30) (MapType0Select a@@50 y@@9))
)))
(assert (forall ((a@@51 T@U) (x@@31 T@U) (y@@10 T@U) ) (! (let ((T@@74 (type x@@31)))
 (=> (and (and (= (type a@@51) (MapType0Type T@@74 intType)) (= (type y@@10) T@@74)) (not (= x@@31 y@@10))) (= (U_2_int (MapType0Select a@@51 y@@10)) (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@51 x@@31) y@@10)))))
 :qid |DafnyPre.806:18|
 :skolemid |496|
 :pattern ( (|MultiSet#UnionOne| a@@51 x@@31) (MapType0Select a@@51 y@@10))
)))
(assert (forall ((a@@52 T@U) (x@@32 T@U) ) (! (let ((T@@75 (type x@@32)))
 (=> (= (type a@@52) (MapType0Type T@@75 intType)) (= (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@32)) (+ (|MultiSet#Card| a@@52) 1))))
 :qid |DafnyPre.808:18|
 :skolemid |497|
 :pattern ( (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@32)))
)))
(assert (forall ((arg0@@81 T@U) (arg1@@32 T@U) ) (! (let ((T@@76 (MapType0TypeInv0 (type arg0@@81))))
(= (type (|MultiSet#Union| arg0@@81 arg1@@32)) (MapType0Type T@@76 intType)))
 :qid |funType:MultiSet#Union|
 :pattern ( (|MultiSet#Union| arg0@@81 arg1@@32))
)))
(assert (forall ((a@@53 T@U) (b@@38 T@U) (o@@43 T@U) ) (! (let ((T@@77 (type o@@43)))
 (=> (and (= (type a@@53) (MapType0Type T@@77 intType)) (= (type b@@38) (MapType0Type T@@77 intType))) (= (U_2_int (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@43)) (+ (U_2_int (MapType0Select a@@53 o@@43)) (U_2_int (MapType0Select b@@38 o@@43))))))
 :qid |DafnyPre.814:18|
 :skolemid |498|
 :pattern ( (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@43))
)))
(assert (forall ((a@@54 T@U) (b@@39 T@U) ) (! (let ((T@@78 (MapType0TypeInv0 (type a@@54))))
 (=> (and (= (type a@@54) (MapType0Type T@@78 intType)) (= (type b@@39) (MapType0Type T@@78 intType))) (= (|MultiSet#Card| (|MultiSet#Union| a@@54 b@@39)) (+ (|MultiSet#Card| a@@54) (|MultiSet#Card| b@@39)))))
 :qid |DafnyPre.816:18|
 :skolemid |499|
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
 :skolemid |500|
 :pattern ( (MapType0Select (|MultiSet#Intersection| a@@55 b@@40) o@@44))
)))
(assert (forall ((a@@56 T@U) (b@@41 T@U) ) (! (let ((T@@81 (MapType0TypeInv0 (type a@@56))))
 (=> (and (= (type a@@56) (MapType0Type T@@81 intType)) (= (type b@@41) (MapType0Type T@@81 intType))) (= (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41) (|MultiSet#Intersection| a@@56 b@@41))))
 :qid |DafnyPre.824:18|
 :skolemid |501|
 :pattern ( (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41))
)))
(assert (forall ((a@@57 T@U) (b@@42 T@U) ) (! (let ((T@@82 (MapType0TypeInv0 (type a@@57))))
 (=> (and (= (type a@@57) (MapType0Type T@@82 intType)) (= (type b@@42) (MapType0Type T@@82 intType))) (= (|MultiSet#Intersection| a@@57 (|MultiSet#Intersection| a@@57 b@@42)) (|MultiSet#Intersection| a@@57 b@@42))))
 :qid |DafnyPre.826:18|
 :skolemid |502|
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
 :skolemid |503|
 :pattern ( (MapType0Select (|MultiSet#Difference| a@@58 b@@43) o@@45))
)))
(assert (forall ((a@@59 T@U) (b@@44 T@U) (y@@11 T@U) ) (! (let ((T@@85 (type y@@11)))
 (=> (and (and (= (type a@@59) (MapType0Type T@@85 intType)) (= (type b@@44) (MapType0Type T@@85 intType))) (<= (U_2_int (MapType0Select a@@59 y@@11)) (U_2_int (MapType0Select b@@44 y@@11)))) (= (U_2_int (MapType0Select (|MultiSet#Difference| a@@59 b@@44) y@@11)) 0)))
 :qid |DafnyPre.833:18|
 :skolemid |504|
 :pattern ( (|MultiSet#Difference| a@@59 b@@44) (MapType0Select b@@44 y@@11) (MapType0Select a@@59 y@@11))
)))
(assert (forall ((a@@60 T@U) (b@@45 T@U) ) (! (let ((T@@86 (MapType0TypeInv0 (type a@@60))))
 (=> (and (= (type a@@60) (MapType0Type T@@86 intType)) (= (type b@@45) (MapType0Type T@@86 intType))) (and (= (+ (+ (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (|MultiSet#Card| (|MultiSet#Difference| b@@45 a@@60))) (* 2 (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))) (|MultiSet#Card| (|MultiSet#Union| a@@60 b@@45))) (= (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (- (|MultiSet#Card| a@@60) (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))))))
 :qid |DafnyPre.835:18|
 :skolemid |505|
 :pattern ( (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)))
)))
(assert (forall ((a@@61 T@U) (b@@46 T@U) ) (! (let ((T@@87 (MapType0TypeInv0 (type a@@61))))
 (=> (and (= (type a@@61) (MapType0Type T@@87 intType)) (= (type b@@46) (MapType0Type T@@87 intType))) (and (=> (|MultiSet#Subset| a@@61 b@@46) (forall ((o@@46 T@U) ) (!  (=> (= (type o@@46) T@@87) (<= (U_2_int (MapType0Select a@@61 o@@46)) (U_2_int (MapType0Select b@@46 o@@46))))
 :qid |DafnyPre.845:37|
 :skolemid |506|
 :pattern ( (MapType0Select a@@61 o@@46))
 :pattern ( (MapType0Select b@@46 o@@46))
))) (=> (forall ((o@@47 T@U) ) (!  (=> (= (type o@@47) T@@87) (<= (U_2_int (MapType0Select a@@61 o@@47)) (U_2_int (MapType0Select b@@46 o@@47))))
 :qid |DafnyPre.845:37|
 :skolemid |506|
 :pattern ( (MapType0Select a@@61 o@@47))
 :pattern ( (MapType0Select b@@46 o@@47))
)) (|MultiSet#Subset| a@@61 b@@46)))))
 :qid |DafnyPre.844:17|
 :skolemid |507|
 :pattern ( (|MultiSet#Subset| a@@61 b@@46))
)))
(assert (forall ((a@@62 T@U) (b@@47 T@U) ) (! (let ((T@@88 (MapType0TypeInv0 (type a@@62))))
 (=> (and (= (type a@@62) (MapType0Type T@@88 intType)) (= (type b@@47) (MapType0Type T@@88 intType))) (and (=> (|MultiSet#Equal| a@@62 b@@47) (forall ((o@@48 T@U) ) (!  (=> (= (type o@@48) T@@88) (= (U_2_int (MapType0Select a@@62 o@@48)) (U_2_int (MapType0Select b@@47 o@@48))))
 :qid |DafnyPre.849:36|
 :skolemid |508|
 :pattern ( (MapType0Select a@@62 o@@48))
 :pattern ( (MapType0Select b@@47 o@@48))
))) (=> (forall ((o@@49 T@U) ) (!  (=> (= (type o@@49) T@@88) (= (U_2_int (MapType0Select a@@62 o@@49)) (U_2_int (MapType0Select b@@47 o@@49))))
 :qid |DafnyPre.849:36|
 :skolemid |508|
 :pattern ( (MapType0Select a@@62 o@@49))
 :pattern ( (MapType0Select b@@47 o@@49))
)) (|MultiSet#Equal| a@@62 b@@47)))))
 :qid |DafnyPre.848:17|
 :skolemid |509|
 :pattern ( (|MultiSet#Equal| a@@62 b@@47))
)))
(assert (forall ((a@@63 T@U) (b@@48 T@U) ) (! (let ((T@@89 (MapType0TypeInv0 (type a@@63))))
 (=> (and (and (= (type a@@63) (MapType0Type T@@89 intType)) (= (type b@@48) (MapType0Type T@@89 intType))) (|MultiSet#Equal| a@@63 b@@48)) (= a@@63 b@@48)))
 :qid |DafnyPre.851:17|
 :skolemid |510|
 :pattern ( (|MultiSet#Equal| a@@63 b@@48))
)))
(assert (forall ((a@@64 T@U) (b@@49 T@U) ) (! (let ((T@@90 (MapType0TypeInv0 (type a@@64))))
 (=> (and (= (type a@@64) (MapType0Type T@@90 intType)) (= (type b@@49) (MapType0Type T@@90 intType))) (and (=> (|MultiSet#Disjoint| a@@64 b@@49) (forall ((o@@50 T@U) ) (!  (=> (= (type o@@50) T@@90) (or (= (U_2_int (MapType0Select a@@64 o@@50)) 0) (= (U_2_int (MapType0Select b@@49 o@@50)) 0)))
 :qid |DafnyPre.856:39|
 :skolemid |511|
 :pattern ( (MapType0Select a@@64 o@@50))
 :pattern ( (MapType0Select b@@49 o@@50))
))) (=> (forall ((o@@51 T@U) ) (!  (=> (= (type o@@51) T@@90) (or (= (U_2_int (MapType0Select a@@64 o@@51)) 0) (= (U_2_int (MapType0Select b@@49 o@@51)) 0)))
 :qid |DafnyPre.856:39|
 :skolemid |511|
 :pattern ( (MapType0Select a@@64 o@@51))
 :pattern ( (MapType0Select b@@49 o@@51))
)) (|MultiSet#Disjoint| a@@64 b@@49)))))
 :qid |DafnyPre.855:18|
 :skolemid |512|
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
 :skolemid |513|
 :pattern ( (MapType0Select (|MultiSet#FromSet| s@@8) a@@65))
)))
(assert (forall ((s@@9 T@U) ) (! (let ((T@@93 (MapType0TypeInv0 (type s@@9))))
 (=> (= (type s@@9) (MapType0Type T@@93 boolType)) (= (|MultiSet#Card| (|MultiSet#FromSet| s@@9)) (|Set#Card| s@@9))))
 :qid |DafnyPre.863:18|
 :skolemid |514|
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
 :skolemid |515|
 :pattern ( (|MultiSet#FromSeq| s@@10))
)))
(assert (forall ((s@@11 T@U) ) (! (let ((T@@96 (SeqTypeInv0 (type s@@11))))
 (=> (= (type s@@11) (SeqType T@@96)) (= (|MultiSet#Card| (|MultiSet#FromSeq| s@@11)) (|Seq#Length| s@@11))))
 :qid |DafnyPre.871:18|
 :skolemid |516|
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
 :skolemid |517|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Build| s@@12 v@@25)))
)))
(assert (forall ((T@@99 T@T) ) (! (= (type (|Seq#Empty| T@@99)) (SeqType T@@99))
 :qid |funType:Seq#Empty|
 :pattern ( (|Seq#Empty| T@@99))
)))
(assert (forall ((T@@100 T@T) ) (! (= (|MultiSet#FromSeq| (|Seq#Empty| T@@100)) (|MultiSet#Empty| T@@100))
 :skolemid |518|
)))
(assert (forall ((arg0@@87 T@U) (arg1@@36 T@U) ) (! (let ((T@@101 (SeqTypeInv0 (type arg0@@87))))
(= (type (|Seq#Append| arg0@@87 arg1@@36)) (SeqType T@@101)))
 :qid |funType:Seq#Append|
 :pattern ( (|Seq#Append| arg0@@87 arg1@@36))
)))
(assert (forall ((a@@66 T@U) (b@@50 T@U) ) (! (let ((T@@102 (SeqTypeInv0 (type a@@66))))
 (=> (and (= (type a@@66) (SeqType T@@102)) (= (type b@@50) (SeqType T@@102))) (= (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)) (|MultiSet#Union| (|MultiSet#FromSeq| a@@66) (|MultiSet#FromSeq| b@@50)))))
 :qid |DafnyPre.882:18|
 :skolemid |519|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)))
)))
(assert (forall ((arg0@@88 T@U) (arg1@@37 Int) (arg2@@1 T@U) ) (! (let ((T@@103 (type arg2@@1)))
(= (type (|Seq#Update| arg0@@88 arg1@@37 arg2@@1)) (SeqType T@@103)))
 :qid |funType:Seq#Update|
 :pattern ( (|Seq#Update| arg0@@88 arg1@@37 arg2@@1))
)))
(assert (forall ((s@@13 T@U) (i@@8 Int) (v@@26 T@U) (x@@33 T@U) ) (! (let ((T@@104 (type v@@26)))
 (=> (and (and (= (type s@@13) (SeqType T@@104)) (= (type x@@33) T@@104)) (and (<= 0 i@@8) (< i@@8 (|Seq#Length| s@@13)))) (= (U_2_int (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@8 v@@26)) x@@33)) (U_2_int (MapType0Select (|MultiSet#Union| (|MultiSet#Difference| (|MultiSet#FromSeq| s@@13) (|MultiSet#Singleton| (|Seq#Index| s@@13 i@@8))) (|MultiSet#Singleton| v@@26)) x@@33)))))
 :qid |DafnyPre.887:18|
 :skolemid |520|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@8 v@@26)) x@@33))
)))
(assert (forall ((s@@14 T@U) (x@@34 T@U) ) (! (let ((T@@105 (type x@@34)))
 (=> (= (type s@@14) (SeqType T@@105)) (and (=> (exists ((i@@9 Int) ) (!  (and (and (<= 0 i@@9) (< i@@9 (|Seq#Length| s@@14))) (= x@@34 (|Seq#Index| s@@14 i@@9)))
 :qid |DafnyPre.894:11|
 :skolemid |521|
 :pattern ( (|Seq#Index| s@@14 i@@9))
)) (< 0 (U_2_int (MapType0Select (|MultiSet#FromSeq| s@@14) x@@34)))) (=> (< 0 (U_2_int (MapType0Select (|MultiSet#FromSeq| s@@14) x@@34))) (exists ((i@@10 Int) ) (!  (and (and (<= 0 i@@10) (< i@@10 (|Seq#Length| s@@14))) (= x@@34 (|Seq#Index| s@@14 i@@10)))
 :qid |DafnyPre.894:11|
 :skolemid |521|
 :pattern ( (|Seq#Index| s@@14 i@@10))
))))))
 :qid |DafnyPre.893:18|
 :skolemid |522|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| s@@14) x@@34))
)))
(assert (forall ((s@@15 T@U) ) (! (let ((T@@106 (SeqTypeInv0 (type s@@15))))
 (=> (= (type s@@15) (SeqType T@@106)) (<= 0 (|Seq#Length| s@@15))))
 :qid |DafnyPre.903:18|
 :skolemid |523|
 :pattern ( (|Seq#Length| s@@15))
)))
(assert (forall ((T@@107 T@T) ) (! (= (|Seq#Length| (|Seq#Empty| T@@107)) 0)
 :skolemid |524|
 :pattern ( (|Seq#Empty| T@@107))
)))
(assert (forall ((s@@16 T@U) ) (! (let ((T@@108 (SeqTypeInv0 (type s@@16))))
 (=> (and (= (type s@@16) (SeqType T@@108)) (= (|Seq#Length| s@@16) 0)) (= s@@16 (|Seq#Empty| T@@108))))
 :qid |DafnyPre.907:18|
 :skolemid |525|
 :pattern ( (|Seq#Length| s@@16))
)))
(assert (forall ((t@@23 T@U) (T@@109 T@T) ) (!  (=> (= (type t@@23) TyType) ($Is (|Seq#Empty| T@@109) t@@23))
 :qid |DafnyPre.917:18|
 :skolemid |526|
 :pattern ( ($Is (|Seq#Empty| T@@109) t@@23))
)))
(assert (forall ((arg0@@89 T@U) ) (! (let ((T@@110 (type arg0@@89)))
(= (type (|Seq#Singleton| arg0@@89)) (SeqType T@@110)))
 :qid |funType:Seq#Singleton|
 :pattern ( (|Seq#Singleton| arg0@@89))
)))
(assert (forall ((t@@24 T@U) ) (! (= (|Seq#Length| (|Seq#Singleton| t@@24)) 1)
 :qid |DafnyPre.920:18|
 :skolemid |527|
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
 :skolemid |528|
 :pattern ( (|Seq#Build| s@@17 val@@5))
)))
(assert (forall ((s@@18 T@U) (v@@27 T@U) ) (! (let ((T@@114 (type v@@27)))
 (=> (= (type s@@18) (SeqType T@@114)) (= (|Seq#Length| (|Seq#Build| s@@18 v@@27)) (+ 1 (|Seq#Length| s@@18)))))
 :qid |DafnyPre.930:18|
 :skolemid |529|
 :pattern ( (|Seq#Build| s@@18 v@@27))
)))
(assert (forall ((s@@19 T@U) (i@@11 Int) (v@@28 T@U) ) (! (let ((T@@115 (type v@@28)))
 (=> (= (type s@@19) (SeqType T@@115)) (and (=> (= i@@11 (|Seq#Length| s@@19)) (= (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11) v@@28)) (=> (not (= i@@11 (|Seq#Length| s@@19))) (= (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11) (|Seq#Index| s@@19 i@@11))))))
 :qid |DafnyPre.933:18|
 :skolemid |530|
 :pattern ( (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11))
)))
(assert (forall ((s@@20 T@U) (bx@@33 T@U) (t@@25 T@U) ) (!  (=> (and (and (and (= (type s@@20) (SeqType BoxType)) (= (type bx@@33) BoxType)) (= (type t@@25) TyType)) (and ($Is s@@20 (TSeq t@@25)) ($IsBox bx@@33 t@@25))) ($Is (|Seq#Build| s@@20 bx@@33) (TSeq t@@25)))
 :qid |DafnyPre.938:15|
 :skolemid |531|
 :pattern ( ($Is (|Seq#Build| s@@20 bx@@33) (TSeq t@@25)))
)))
(assert  (and (= (Ctor HandleTypeType) 22) (forall ((arg0@@92 T@U) (arg1@@38 T@U) (arg2@@2 Int) (arg3 T@U) ) (! (= (type (|Seq#Create| arg0@@92 arg1@@38 arg2@@2 arg3)) (SeqType BoxType))
 :qid |funType:Seq#Create|
 :pattern ( (|Seq#Create| arg0@@92 arg1@@38 arg2@@2 arg3))
))))
(assert (forall ((ty T@U) (heap T@U) (len Int) (init T@U) ) (!  (=> (and (and (and (= (type ty) TyType) (= (type heap) (MapType0Type refType MapType1Type))) (= (type init) HandleTypeType)) (and ($IsGoodHeap heap) (<= 0 len))) (= (|Seq#Length| (|Seq#Create| ty heap len init)) len))
 :qid |DafnyPre.942:15|
 :skolemid |532|
 :pattern ( (|Seq#Length| (|Seq#Create| ty heap len init)))
)))
(assert (forall ((arg0@@93 T@U) (arg1@@39 T@U) (arg2@@3 T@U) (arg3@@0 T@U) (arg4 T@U) ) (! (= (type (Apply1 arg0@@93 arg1@@39 arg2@@3 arg3@@0 arg4)) BoxType)
 :qid |funType:Apply1|
 :pattern ( (Apply1 arg0@@93 arg1@@39 arg2@@3 arg3@@0 arg4))
)))
(assert (forall ((ty@@0 T@U) (heap@@0 T@U) (len@@0 Int) (init@@0 T@U) (i@@12 Int) ) (!  (=> (and (and (and (= (type ty@@0) TyType) (= (type heap@@0) (MapType0Type refType MapType1Type))) (= (type init@@0) HandleTypeType)) (and (and ($IsGoodHeap heap@@0) (<= 0 i@@12)) (< i@@12 len@@0))) (= (|Seq#Index| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@12) (Apply1 TInt (TSeq ty@@0) heap@@0 init@@0 ($Box (int_2_U i@@12)))))
 :qid |DafnyPre.946:15|
 :skolemid |533|
 :pattern ( (|Seq#Index| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@12))
)))
(assert (forall ((s0 T@U) (s1 T@U) ) (! (let ((T@@116 (SeqTypeInv0 (type s0))))
 (=> (and (= (type s0) (SeqType T@@116)) (= (type s1) (SeqType T@@116))) (= (|Seq#Length| (|Seq#Append| s0 s1)) (+ (|Seq#Length| s0) (|Seq#Length| s1)))))
 :qid |DafnyPre.952:18|
 :skolemid |534|
 :pattern ( (|Seq#Length| (|Seq#Append| s0 s1)))
)))
(assert (forall ((s0@@0 T@U) (s1@@0 T@U) (t@@26 T@U) ) (!  (=> (and (and (and (= (type s0@@0) (SeqType BoxType)) (= (type s1@@0) (SeqType BoxType))) (= (type t@@26) TyType)) (and ($Is s0@@0 t@@26) ($Is s1@@0 t@@26))) ($Is (|Seq#Append| s0@@0 s1@@0) t@@26))
 :qid |DafnyPre.956:15|
 :skolemid |535|
 :pattern ( ($Is (|Seq#Append| s0@@0 s1@@0) t@@26))
)))
(assert (forall ((t@@27 T@U) ) (! (= (|Seq#Index| (|Seq#Singleton| t@@27) 0) t@@27)
 :qid |DafnyPre.960:18|
 :skolemid |536|
 :pattern ( (|Seq#Index| (|Seq#Singleton| t@@27) 0))
)))
(assert (forall ((s0@@1 T@U) (s1@@1 T@U) (n@@6 Int) ) (! (let ((T@@117 (SeqTypeInv0 (type s0@@1))))
 (=> (and (= (type s0@@1) (SeqType T@@117)) (= (type s1@@1) (SeqType T@@117))) (and (=> (< n@@6 (|Seq#Length| s0@@1)) (= (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6) (|Seq#Index| s0@@1 n@@6))) (=> (<= (|Seq#Length| s0@@1) n@@6) (= (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6) (|Seq#Index| s1@@1 (- n@@6 (|Seq#Length| s0@@1))))))))
 :qid |DafnyPre.961:18|
 :skolemid |537|
 :pattern ( (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6))
)))
(assert (forall ((s@@21 T@U) (i@@13 Int) (v@@29 T@U) ) (! (let ((T@@118 (type v@@29)))
 (=> (= (type s@@21) (SeqType T@@118)) (=> (and (<= 0 i@@13) (< i@@13 (|Seq#Length| s@@21))) (= (|Seq#Length| (|Seq#Update| s@@21 i@@13 v@@29)) (|Seq#Length| s@@21)))))
 :qid |DafnyPre.966:18|
 :skolemid |538|
 :pattern ( (|Seq#Length| (|Seq#Update| s@@21 i@@13 v@@29)))
)))
(assert (forall ((s@@22 T@U) (i@@14 Int) (v@@30 T@U) (n@@7 Int) ) (! (let ((T@@119 (type v@@30)))
 (=> (= (type s@@22) (SeqType T@@119)) (=> (and (<= 0 n@@7) (< n@@7 (|Seq#Length| s@@22))) (and (=> (= i@@14 n@@7) (= (|Seq#Index| (|Seq#Update| s@@22 i@@14 v@@30) n@@7) v@@30)) (=> (not (= i@@14 n@@7)) (= (|Seq#Index| (|Seq#Update| s@@22 i@@14 v@@30) n@@7) (|Seq#Index| s@@22 n@@7)))))))
 :qid |DafnyPre.968:18|
 :skolemid |539|
 :pattern ( (|Seq#Index| (|Seq#Update| s@@22 i@@14 v@@30) n@@7))
)))
(assert (forall ((s@@23 T@U) (x@@35 T@U) ) (! (let ((T@@120 (type x@@35)))
 (=> (= (type s@@23) (SeqType T@@120)) (and (=> (|Seq#Contains| s@@23 x@@35) (exists ((i@@15 Int) ) (!  (and (and (<= 0 i@@15) (< i@@15 (|Seq#Length| s@@23))) (= (|Seq#Index| s@@23 i@@15) x@@35))
 :qid |DafnyPre.976:13|
 :skolemid |540|
 :pattern ( (|Seq#Index| s@@23 i@@15))
))) (=> (exists ((i@@16 Int) ) (!  (and (and (<= 0 i@@16) (< i@@16 (|Seq#Length| s@@23))) (= (|Seq#Index| s@@23 i@@16) x@@35))
 :qid |DafnyPre.976:13|
 :skolemid |540|
 :pattern ( (|Seq#Index| s@@23 i@@16))
)) (|Seq#Contains| s@@23 x@@35)))))
 :qid |DafnyPre.974:18|
 :skolemid |541|
 :pattern ( (|Seq#Contains| s@@23 x@@35))
)))
(assert (forall ((x@@36 T@U) ) (! (let ((T@@121 (type x@@36)))
 (not (|Seq#Contains| (|Seq#Empty| T@@121) x@@36)))
 :qid |DafnyPre.977:18|
 :skolemid |542|
 :pattern ( (let ((T@@121 (type x@@36)))
(|Seq#Contains| (|Seq#Empty| T@@121) x@@36)))
)))
(assert (forall ((s0@@2 T@U) (s1@@2 T@U) (x@@37 T@U) ) (! (let ((T@@122 (type x@@37)))
 (=> (and (= (type s0@@2) (SeqType T@@122)) (= (type s1@@2) (SeqType T@@122))) (and (=> (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@37) (or (|Seq#Contains| s0@@2 x@@37) (|Seq#Contains| s1@@2 x@@37))) (=> (or (|Seq#Contains| s0@@2 x@@37) (|Seq#Contains| s1@@2 x@@37)) (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@37)))))
 :qid |DafnyPre.981:18|
 :skolemid |543|
 :pattern ( (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@37))
)))
(assert (forall ((s@@24 T@U) (v@@31 T@U) (x@@38 T@U) ) (! (let ((T@@123 (type v@@31)))
 (=> (and (= (type s@@24) (SeqType T@@123)) (= (type x@@38) T@@123)) (and (=> (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@38) (or (= v@@31 x@@38) (|Seq#Contains| s@@24 x@@38))) (=> (or (= v@@31 x@@38) (|Seq#Contains| s@@24 x@@38)) (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@38)))))
 :qid |DafnyPre.986:18|
 :skolemid |544|
 :pattern ( (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@38))
)))
(assert (forall ((arg0@@94 T@U) (arg1@@40 Int) ) (! (let ((T@@124 (SeqTypeInv0 (type arg0@@94))))
(= (type (|Seq#Take| arg0@@94 arg1@@40)) (SeqType T@@124)))
 :qid |funType:Seq#Take|
 :pattern ( (|Seq#Take| arg0@@94 arg1@@40))
)))
(assert (forall ((s@@25 T@U) (n@@8 Int) (x@@39 T@U) ) (! (let ((T@@125 (type x@@39)))
 (=> (= (type s@@25) (SeqType T@@125)) (and (=> (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@39) (exists ((i@@17 Int) ) (!  (and (and (and (<= 0 i@@17) (< i@@17 n@@8)) (< i@@17 (|Seq#Length| s@@25))) (= (|Seq#Index| s@@25 i@@17) x@@39))
 :qid |DafnyPre.993:13|
 :skolemid |545|
 :pattern ( (|Seq#Index| s@@25 i@@17))
))) (=> (exists ((i@@18 Int) ) (!  (and (and (and (<= 0 i@@18) (< i@@18 n@@8)) (< i@@18 (|Seq#Length| s@@25))) (= (|Seq#Index| s@@25 i@@18) x@@39))
 :qid |DafnyPre.993:13|
 :skolemid |545|
 :pattern ( (|Seq#Index| s@@25 i@@18))
)) (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@39)))))
 :qid |DafnyPre.990:18|
 :skolemid |546|
 :pattern ( (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@39))
)))
(assert (forall ((arg0@@95 T@U) (arg1@@41 Int) ) (! (let ((T@@126 (SeqTypeInv0 (type arg0@@95))))
(= (type (|Seq#Drop| arg0@@95 arg1@@41)) (SeqType T@@126)))
 :qid |funType:Seq#Drop|
 :pattern ( (|Seq#Drop| arg0@@95 arg1@@41))
)))
(assert (forall ((s@@26 T@U) (n@@9 Int) (x@@40 T@U) ) (! (let ((T@@127 (type x@@40)))
 (=> (= (type s@@26) (SeqType T@@127)) (and (=> (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@40) (exists ((i@@19 Int) ) (!  (and (and (and (<= 0 n@@9) (<= n@@9 i@@19)) (< i@@19 (|Seq#Length| s@@26))) (= (|Seq#Index| s@@26 i@@19) x@@40))
 :qid |DafnyPre.998:13|
 :skolemid |547|
 :pattern ( (|Seq#Index| s@@26 i@@19))
))) (=> (exists ((i@@20 Int) ) (!  (and (and (and (<= 0 n@@9) (<= n@@9 i@@20)) (< i@@20 (|Seq#Length| s@@26))) (= (|Seq#Index| s@@26 i@@20) x@@40))
 :qid |DafnyPre.998:13|
 :skolemid |547|
 :pattern ( (|Seq#Index| s@@26 i@@20))
)) (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@40)))))
 :qid |DafnyPre.995:18|
 :skolemid |548|
 :pattern ( (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@40))
)))
(assert (forall ((s0@@3 T@U) (s1@@3 T@U) ) (! (let ((T@@128 (SeqTypeInv0 (type s0@@3))))
 (=> (and (= (type s0@@3) (SeqType T@@128)) (= (type s1@@3) (SeqType T@@128))) (and (=> (|Seq#Equal| s0@@3 s1@@3) (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j Int) ) (!  (=> (and (<= 0 j) (< j (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j) (|Seq#Index| s1@@3 j)))
 :qid |DafnyPre.1005:13|
 :skolemid |549|
 :pattern ( (|Seq#Index| s0@@3 j))
 :pattern ( (|Seq#Index| s1@@3 j))
)))) (=> (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j@@0) (|Seq#Index| s1@@3 j@@0)))
 :qid |DafnyPre.1005:13|
 :skolemid |549|
 :pattern ( (|Seq#Index| s0@@3 j@@0))
 :pattern ( (|Seq#Index| s1@@3 j@@0))
))) (|Seq#Equal| s0@@3 s1@@3)))))
 :qid |DafnyPre.1002:18|
 :skolemid |550|
 :pattern ( (|Seq#Equal| s0@@3 s1@@3))
)))
(assert (forall ((a@@67 T@U) (b@@51 T@U) ) (! (let ((T@@129 (SeqTypeInv0 (type a@@67))))
 (=> (and (and (= (type a@@67) (SeqType T@@129)) (= (type b@@51) (SeqType T@@129))) (|Seq#Equal| a@@67 b@@51)) (= a@@67 b@@51)))
 :qid |DafnyPre.1007:18|
 :skolemid |551|
 :pattern ( (|Seq#Equal| a@@67 b@@51))
)))
(assert (forall ((s0@@4 T@U) (s1@@4 T@U) (n@@10 Int) ) (! (let ((T@@130 (SeqTypeInv0 (type s0@@4))))
 (=> (and (= (type s0@@4) (SeqType T@@130)) (= (type s1@@4) (SeqType T@@130))) (and (=> (|Seq#SameUntil| s0@@4 s1@@4 n@@10) (forall ((j@@1 Int) ) (!  (=> (and (<= 0 j@@1) (< j@@1 n@@10)) (= (|Seq#Index| s0@@4 j@@1) (|Seq#Index| s1@@4 j@@1)))
 :qid |DafnyPre.1013:13|
 :skolemid |552|
 :pattern ( (|Seq#Index| s0@@4 j@@1))
 :pattern ( (|Seq#Index| s1@@4 j@@1))
))) (=> (forall ((j@@2 Int) ) (!  (=> (and (<= 0 j@@2) (< j@@2 n@@10)) (= (|Seq#Index| s0@@4 j@@2) (|Seq#Index| s1@@4 j@@2)))
 :qid |DafnyPre.1013:13|
 :skolemid |552|
 :pattern ( (|Seq#Index| s0@@4 j@@2))
 :pattern ( (|Seq#Index| s1@@4 j@@2))
)) (|Seq#SameUntil| s0@@4 s1@@4 n@@10)))))
 :qid |DafnyPre.1011:18|
 :skolemid |553|
 :pattern ( (|Seq#SameUntil| s0@@4 s1@@4 n@@10))
)))
(assert (forall ((s@@27 T@U) (n@@11 Int) ) (! (let ((T@@131 (SeqTypeInv0 (type s@@27))))
 (=> (= (type s@@27) (SeqType T@@131)) (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length| s@@27))) (= (|Seq#Length| (|Seq#Take| s@@27 n@@11)) n@@11))))
 :qid |DafnyPre.1017:18|
 :skolemid |554|
 :pattern ( (|Seq#Length| (|Seq#Take| s@@27 n@@11)))
)))
(assert (forall ((s@@28 T@U) (n@@12 Int) (j@@3 Int) ) (! (let ((T@@132 (SeqTypeInv0 (type s@@28))))
 (=> (= (type s@@28) (SeqType T@@132)) (=> (and (and (<= 0 j@@3) (< j@@3 n@@12)) (< j@@3 (|Seq#Length| s@@28))) (= (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@3) (|Seq#Index| s@@28 j@@3)))))
 :qid |DafnyPre.1019:18|
 :weight 25
 :skolemid |555|
 :pattern ( (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@3))
 :pattern ( (|Seq#Index| s@@28 j@@3) (|Seq#Take| s@@28 n@@12))
)))
(assert (forall ((s@@29 T@U) (n@@13 Int) ) (! (let ((T@@133 (SeqTypeInv0 (type s@@29))))
 (=> (= (type s@@29) (SeqType T@@133)) (=> (and (<= 0 n@@13) (<= n@@13 (|Seq#Length| s@@29))) (= (|Seq#Length| (|Seq#Drop| s@@29 n@@13)) (- (|Seq#Length| s@@29) n@@13)))))
 :qid |DafnyPre.1027:18|
 :skolemid |556|
 :pattern ( (|Seq#Length| (|Seq#Drop| s@@29 n@@13)))
)))
(assert (forall ((s@@30 T@U) (n@@14 Int) (j@@4 Int) ) (! (let ((T@@134 (SeqTypeInv0 (type s@@30))))
 (=> (= (type s@@30) (SeqType T@@134)) (=> (and (and (<= 0 n@@14) (<= 0 j@@4)) (< j@@4 (- (|Seq#Length| s@@30) n@@14))) (= (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@4) (|Seq#Index| s@@30 (+ j@@4 n@@14))))))
 :qid |DafnyPre.1029:18|
 :weight 25
 :skolemid |557|
 :pattern ( (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@4))
)))
(assert (forall ((s@@31 T@U) (n@@15 Int) (k@@3 Int) ) (! (let ((T@@135 (SeqTypeInv0 (type s@@31))))
 (=> (= (type s@@31) (SeqType T@@135)) (=> (and (and (<= 0 n@@15) (<= n@@15 k@@3)) (< k@@3 (|Seq#Length| s@@31))) (= (|Seq#Index| (|Seq#Drop| s@@31 n@@15) (- k@@3 n@@15)) (|Seq#Index| s@@31 k@@3)))))
 :qid |DafnyPre.1034:18|
 :weight 25
 :skolemid |558|
 :pattern ( (|Seq#Index| s@@31 k@@3) (|Seq#Drop| s@@31 n@@15))
)))
(assert (forall ((s@@32 T@U) (t@@28 T@U) (n@@16 Int) ) (! (let ((T@@136 (SeqTypeInv0 (type s@@32))))
 (=> (and (and (= (type s@@32) (SeqType T@@136)) (= (type t@@28) (SeqType T@@136))) (= n@@16 (|Seq#Length| s@@32))) (and (= (|Seq#Take| (|Seq#Append| s@@32 t@@28) n@@16) s@@32) (= (|Seq#Drop| (|Seq#Append| s@@32 t@@28) n@@16) t@@28))))
 :qid |DafnyPre.1040:18|
 :skolemid |559|
 :pattern ( (|Seq#Take| (|Seq#Append| s@@32 t@@28) n@@16))
 :pattern ( (|Seq#Drop| (|Seq#Append| s@@32 t@@28) n@@16))
)))
(assert (forall ((arg0@@96 T@U) (arg1@@42 T@U) ) (! (= (type (|Seq#FromArray| arg0@@96 arg1@@42)) (SeqType BoxType))
 :qid |funType:Seq#FromArray|
 :pattern ( (|Seq#FromArray| arg0@@96 arg1@@42))
)))
(assert (forall ((h@@16 T@U) (a@@68 T@U) ) (!  (=> (and (= (type h@@16) (MapType0Type refType MapType1Type)) (= (type a@@68) refType)) (= (|Seq#Length| (|Seq#FromArray| h@@16 a@@68)) (_System.array.Length a@@68)))
 :qid |DafnyPre.1049:15|
 :skolemid |560|
 :pattern ( (|Seq#Length| (|Seq#FromArray| h@@16 a@@68)))
)))
(assert (forall ((h@@17 T@U) (a@@69 T@U) ) (!  (=> (and (= (type h@@17) (MapType0Type refType MapType1Type)) (= (type a@@69) refType)) (forall ((i@@21 Int) ) (!  (=> (and (<= 0 i@@21) (< i@@21 (|Seq#Length| (|Seq#FromArray| h@@17 a@@69)))) (= (|Seq#Index| (|Seq#FromArray| h@@17 a@@69) i@@21) (MapType1Select (MapType0Select h@@17 a@@69) (IndexField i@@21))))
 :qid |DafnyPre.1054:11|
 :skolemid |561|
 :pattern ( (MapType1Select (MapType0Select h@@17 a@@69) (IndexField i@@21)))
 :pattern ( (|Seq#Index| (|Seq#FromArray| h@@17 a@@69) i@@21))
)))
 :qid |DafnyPre.1052:15|
 :skolemid |562|
 :pattern ( (|Seq#FromArray| h@@17 a@@69))
)))
(assert (forall ((h0 T@U) (h1 T@U) (a@@70 T@U) ) (!  (=> (and (and (= (type h0) (MapType0Type refType MapType1Type)) (= (type h1) (MapType0Type refType MapType1Type))) (= (type a@@70) refType)) (=> (and (and (and ($IsGoodHeap h0) ($IsGoodHeap h1)) ($HeapSucc h0 h1)) (= (MapType0Select h0 a@@70) (MapType0Select h1 a@@70))) (= (|Seq#FromArray| h0 a@@70) (|Seq#FromArray| h1 a@@70))))
 :qid |DafnyPre.1064:15|
 :skolemid |563|
 :pattern ( (|Seq#FromArray| h1 a@@70) ($HeapSucc h0 h1))
)))
(assert (forall ((h@@18 T@U) (i@@22 Int) (v@@32 T@U) (a@@71 T@U) ) (!  (=> (and (and (and (= (type h@@18) (MapType0Type refType MapType1Type)) (= (type v@@32) BoxType)) (= (type a@@71) refType)) (and (<= 0 i@@22) (< i@@22 (_System.array.Length a@@71)))) (= (|Seq#FromArray| (MapType0Store h@@18 a@@71 (MapType1Store (MapType0Select h@@18 a@@71) (IndexField i@@22) v@@32)) a@@71) (|Seq#Update| (|Seq#FromArray| h@@18 a@@71) i@@22 v@@32)))
 :qid |DafnyPre.1069:15|
 :skolemid |564|
 :pattern ( (|Seq#FromArray| (MapType0Store h@@18 a@@71 (MapType1Store (MapType0Select h@@18 a@@71) (IndexField i@@22) v@@32)) a@@71))
)))
(assert (forall ((s@@33 T@U) (i@@23 Int) (v@@33 T@U) (n@@17 Int) ) (! (let ((T@@137 (type v@@33)))
 (=> (= (type s@@33) (SeqType T@@137)) (=> (and (and (<= 0 i@@23) (< i@@23 n@@17)) (<= n@@17 (|Seq#Length| s@@33))) (= (|Seq#Take| (|Seq#Update| s@@33 i@@23 v@@33) n@@17) (|Seq#Update| (|Seq#Take| s@@33 n@@17) i@@23 v@@33)))))
 :qid |DafnyPre.1074:18|
 :skolemid |565|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@33 i@@23 v@@33) n@@17))
)))
(assert (forall ((s@@34 T@U) (i@@24 Int) (v@@34 T@U) (n@@18 Int) ) (! (let ((T@@138 (type v@@34)))
 (=> (= (type s@@34) (SeqType T@@138)) (=> (and (<= n@@18 i@@24) (< i@@24 (|Seq#Length| s@@34))) (= (|Seq#Take| (|Seq#Update| s@@34 i@@24 v@@34) n@@18) (|Seq#Take| s@@34 n@@18)))))
 :qid |DafnyPre.1077:18|
 :skolemid |566|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@34 i@@24 v@@34) n@@18))
)))
(assert (forall ((s@@35 T@U) (i@@25 Int) (v@@35 T@U) (n@@19 Int) ) (! (let ((T@@139 (type v@@35)))
 (=> (= (type s@@35) (SeqType T@@139)) (=> (and (and (<= 0 n@@19) (<= n@@19 i@@25)) (< i@@25 (|Seq#Length| s@@35))) (= (|Seq#Drop| (|Seq#Update| s@@35 i@@25 v@@35) n@@19) (|Seq#Update| (|Seq#Drop| s@@35 n@@19) (- i@@25 n@@19) v@@35)))))
 :qid |DafnyPre.1080:18|
 :skolemid |567|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@35 i@@25 v@@35) n@@19))
)))
(assert (forall ((s@@36 T@U) (i@@26 Int) (v@@36 T@U) (n@@20 Int) ) (! (let ((T@@140 (type v@@36)))
 (=> (= (type s@@36) (SeqType T@@140)) (=> (and (and (<= 0 i@@26) (< i@@26 n@@20)) (< n@@20 (|Seq#Length| s@@36))) (= (|Seq#Drop| (|Seq#Update| s@@36 i@@26 v@@36) n@@20) (|Seq#Drop| s@@36 n@@20)))))
 :qid |DafnyPre.1083:18|
 :skolemid |568|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@36 i@@26 v@@36) n@@20))
)))
(assert (forall ((h@@19 T@U) (a@@72 T@U) (n0 Int) (n1 Int) ) (!  (=> (and (= (type h@@19) (MapType0Type refType MapType1Type)) (= (type a@@72) refType)) (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@72))) (= (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n1) (|Seq#Build| (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n0) (MapType1Select (MapType0Select h@@19 a@@72) (IndexField n0))))))
 :qid |DafnyPre.1087:15|
 :skolemid |569|
 :pattern ( (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n0) (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n1))
)))
(assert (forall ((s@@37 T@U) (v@@37 T@U) (n@@21 Int) ) (! (let ((T@@141 (type v@@37)))
 (=> (= (type s@@37) (SeqType T@@141)) (=> (and (<= 0 n@@21) (<= n@@21 (|Seq#Length| s@@37))) (= (|Seq#Drop| (|Seq#Build| s@@37 v@@37) n@@21) (|Seq#Build| (|Seq#Drop| s@@37 n@@21) v@@37)))))
 :qid |DafnyPre.1091:18|
 :skolemid |570|
 :pattern ( (|Seq#Drop| (|Seq#Build| s@@37 v@@37) n@@21))
)))
(assert (forall ((s@@38 T@U) (i@@27 Int) ) (!  (=> (= (type s@@38) (SeqType BoxType)) (=> (and (<= 0 i@@27) (< i@@27 (|Seq#Length| s@@38))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@27))) (|Seq#Rank| s@@38))))
 :qid |DafnyPre.1096:15|
 :skolemid |571|
 :pattern ( (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@27))))
)))
(assert (forall ((s@@39 T@U) (i@@28 Int) ) (! (let ((T@@142 (SeqTypeInv0 (type s@@39))))
 (=> (= (type s@@39) (SeqType T@@142)) (=> (and (< 0 i@@28) (<= i@@28 (|Seq#Length| s@@39))) (< (|Seq#Rank| (|Seq#Drop| s@@39 i@@28)) (|Seq#Rank| s@@39)))))
 :qid |DafnyPre.1099:18|
 :skolemid |572|
 :pattern ( (|Seq#Rank| (|Seq#Drop| s@@39 i@@28)))
)))
(assert (forall ((s@@40 T@U) (i@@29 Int) ) (! (let ((T@@143 (SeqTypeInv0 (type s@@40))))
 (=> (= (type s@@40) (SeqType T@@143)) (=> (and (<= 0 i@@29) (< i@@29 (|Seq#Length| s@@40))) (< (|Seq#Rank| (|Seq#Take| s@@40 i@@29)) (|Seq#Rank| s@@40)))))
 :qid |DafnyPre.1102:18|
 :skolemid |573|
 :pattern ( (|Seq#Rank| (|Seq#Take| s@@40 i@@29)))
)))
(assert (forall ((s@@41 T@U) (i@@30 Int) (j@@5 Int) ) (! (let ((T@@144 (SeqTypeInv0 (type s@@41))))
 (=> (= (type s@@41) (SeqType T@@144)) (=> (and (and (<= 0 i@@30) (< i@@30 j@@5)) (<= j@@5 (|Seq#Length| s@@41))) (< (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@30) (|Seq#Drop| s@@41 j@@5))) (|Seq#Rank| s@@41)))))
 :qid |DafnyPre.1105:18|
 :skolemid |574|
 :pattern ( (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@30) (|Seq#Drop| s@@41 j@@5))))
)))
(assert (forall ((s@@42 T@U) (n@@22 Int) ) (! (let ((T@@145 (SeqTypeInv0 (type s@@42))))
 (=> (and (= (type s@@42) (SeqType T@@145)) (= n@@22 0)) (= (|Seq#Drop| s@@42 n@@22) s@@42)))
 :qid |DafnyPre.1110:18|
 :skolemid |575|
 :pattern ( (|Seq#Drop| s@@42 n@@22))
)))
(assert (forall ((s@@43 T@U) (n@@23 Int) ) (! (let ((T@@146 (SeqTypeInv0 (type s@@43))))
 (=> (and (= (type s@@43) (SeqType T@@146)) (= n@@23 0)) (= (|Seq#Take| s@@43 n@@23) (|Seq#Empty| T@@146))))
 :qid |DafnyPre.1112:18|
 :skolemid |576|
 :pattern ( (|Seq#Take| s@@43 n@@23))
)))
(assert (forall ((s@@44 T@U) (m@@9 Int) (n@@24 Int) ) (! (let ((T@@147 (SeqTypeInv0 (type s@@44))))
 (=> (= (type s@@44) (SeqType T@@147)) (=> (and (and (<= 0 m@@9) (<= 0 n@@24)) (<= (+ m@@9 n@@24) (|Seq#Length| s@@44))) (= (|Seq#Drop| (|Seq#Drop| s@@44 m@@9) n@@24) (|Seq#Drop| s@@44 (+ m@@9 n@@24))))))
 :qid |DafnyPre.1114:18|
 :skolemid |577|
 :pattern ( (|Seq#Drop| (|Seq#Drop| s@@44 m@@9) n@@24))
)))
(assert (forall ((m@@10 T@U) ) (! (let ((V@@1 (MapTypeInv1 (type m@@10))))
(let ((U@@3 (MapTypeInv0 (type m@@10))))
 (=> (= (type m@@10) (MapType U@@3 V@@1)) (<= 0 (|Map#Card| m@@10)))))
 :qid |DafnyPre.1132:20|
 :skolemid |578|
 :pattern ( (|Map#Card| m@@10))
)))
(assert (forall ((m@@11 T@U) ) (! (let ((V@@2 (MapTypeInv1 (type m@@11))))
(let ((U@@4 (MapTypeInv0 (type m@@11))))
 (=> (= (type m@@11) (MapType U@@4 V@@2)) (= (|Set#Card| (|Map#Domain| m@@11)) (|Map#Card| m@@11)))))
 :qid |DafnyPre.1137:20|
 :skolemid |579|
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
 :skolemid |580|
 :pattern ( (MapType0Select (|Map#Domain| m@@12) u@@5))
 :pattern ( (MapType0Select (|Map#Elements| m@@12) u@@5))
))) (=> (exists ((u@@6 T@U) ) (!  (and (= (type u@@6) U@@5) (and (U_2_bool (MapType0Select (|Map#Domain| m@@12) u@@6)) (= v@@38 (MapType0Select (|Map#Elements| m@@12) u@@6))))
 :qid |DafnyPre.1149:10|
 :skolemid |580|
 :pattern ( (MapType0Select (|Map#Domain| m@@12) u@@6))
 :pattern ( (MapType0Select (|Map#Elements| m@@12) u@@6))
)) (U_2_bool (MapType0Select (|Map#Values| m@@12) v@@38)))))))
 :qid |DafnyPre.1147:20|
 :skolemid |581|
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
 :skolemid |582|
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
 :skolemid |583|
 :pattern ( (MapType0Select (|Map#Items| m@@14) item))
)))
(assert (forall ((U@@7 T@T) (V@@6 T@T) ) (! (= (type (|Map#Empty| U@@7 V@@6)) (MapType U@@7 V@@6))
 :qid |funType:Map#Empty|
 :pattern ( (|Map#Empty| U@@7 V@@6))
)))
(assert (forall ((u@@7 T@U) (V@@7 T@T) ) (! (let ((U@@8 (type u@@7)))
 (not (U_2_bool (MapType0Select (|Map#Domain| (|Map#Empty| U@@8 V@@7)) u@@7))))
 :qid |DafnyPre.1179:21|
 :skolemid |584|
 :pattern ( (let ((U@@8 (type u@@7)))
(MapType0Select (|Map#Domain| (|Map#Empty| U@@8 V@@7)) u@@7)))
)))
(assert (forall ((m@@15 T@U) ) (! (let ((V@@8 (MapTypeInv1 (type m@@15))))
(let ((U@@9 (MapTypeInv0 (type m@@15))))
 (=> (= (type m@@15) (MapType U@@9 V@@8)) (and (and (=> (= (|Map#Card| m@@15) 0) (= m@@15 (|Map#Empty| U@@9 V@@8))) (=> (= m@@15 (|Map#Empty| U@@9 V@@8)) (= (|Map#Card| m@@15) 0))) (=> (not (= (|Map#Card| m@@15) 0)) (exists ((x@@41 T@U) ) (!  (and (= (type x@@41) U@@9) (U_2_bool (MapType0Select (|Map#Domain| m@@15) x@@41)))
 :qid |DafnyPre.1184:32|
 :skolemid |585|
 :no-pattern (type x@@41)
 :no-pattern (U_2_int x@@41)
 :no-pattern (U_2_bool x@@41)
)))))))
 :qid |DafnyPre.1182:21|
 :skolemid |586|
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
 :skolemid |587|
 :pattern ( (|Map#Domain| (|Map#Glue| a@@73 b@@52 t@@29)))
)))
(assert (forall ((a@@74 T@U) (b@@53 T@U) (t@@30 T@U) ) (! (let ((V@@11 (MapType0TypeInv1 (type b@@53))))
(let ((U@@12 (MapType0TypeInv0 (type a@@74))))
 (=> (and (and (= (type a@@74) (MapType0Type U@@12 boolType)) (= (type b@@53) (MapType0Type U@@12 V@@11))) (= (type t@@30) TyType)) (= (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@30)) b@@53))))
 :qid |DafnyPre.1190:21|
 :skolemid |588|
 :pattern ( (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@30)))
)))
(assert (forall ((a@@75 T@U) (b@@54 T@U) (t@@31 T@U) ) (! (let ((V@@12 (MapType0TypeInv1 (type b@@54))))
(let ((U@@13 (MapType0TypeInv0 (type a@@75))))
 (=> (and (and (= (type a@@75) (MapType0Type U@@13 boolType)) (= (type b@@54) (MapType0Type U@@13 V@@12))) (= (type t@@31) TyType)) ($Is (|Map#Glue| a@@75 b@@54 t@@31) t@@31))))
 :qid |DafnyPre.1193:21|
 :skolemid |589|
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
 :skolemid |590|
 :pattern ( (MapType0Select (|Map#Domain| (|Map#Build| m@@16 u@@8 v@@39)) |u'|))
 :pattern ( (MapType0Select (|Map#Elements| (|Map#Build| m@@16 u@@8 v@@39)) |u'|))
)))
(assert (forall ((m@@17 T@U) (u@@9 T@U) (v@@40 T@U) ) (! (let ((V@@15 (type v@@40)))
(let ((U@@16 (type u@@9)))
 (=> (and (= (type m@@17) (MapType U@@16 V@@15)) (U_2_bool (MapType0Select (|Map#Domain| m@@17) u@@9))) (= (|Map#Card| (|Map#Build| m@@17 u@@9 v@@40)) (|Map#Card| m@@17)))))
 :qid |DafnyPre.1210:21|
 :skolemid |591|
 :pattern ( (|Map#Card| (|Map#Build| m@@17 u@@9 v@@40)))
)))
(assert (forall ((m@@18 T@U) (u@@10 T@U) (v@@41 T@U) ) (! (let ((V@@16 (type v@@41)))
(let ((U@@17 (type u@@10)))
 (=> (and (= (type m@@18) (MapType U@@17 V@@16)) (not (U_2_bool (MapType0Select (|Map#Domain| m@@18) u@@10)))) (= (|Map#Card| (|Map#Build| m@@18 u@@10 v@@41)) (+ (|Map#Card| m@@18) 1)))))
 :qid |DafnyPre.1212:21|
 :skolemid |592|
 :pattern ( (|Map#Card| (|Map#Build| m@@18 u@@10 v@@41)))
)))
(assert (forall ((m@@19 T@U) (|m'| T@U) ) (! (let ((V@@17 (MapTypeInv1 (type m@@19))))
(let ((U@@18 (MapTypeInv0 (type m@@19))))
 (=> (and (= (type m@@19) (MapType U@@18 V@@17)) (= (type |m'|) (MapType U@@18 V@@17))) (and (=> (|Map#Equal| m@@19 |m'|) (and (forall ((u@@11 T@U) ) (!  (=> (= (type u@@11) U@@18) (and (=> (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@11)) (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@11))) (=> (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@11)) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@11)))))
 :qid |DafnyPre.1219:35|
 :skolemid |593|
 :no-pattern (type u@@11)
 :no-pattern (U_2_int u@@11)
 :no-pattern (U_2_bool u@@11)
)) (forall ((u@@12 T@U) ) (!  (=> (and (= (type u@@12) U@@18) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@12))) (= (MapType0Select (|Map#Elements| m@@19) u@@12) (MapType0Select (|Map#Elements| |m'|) u@@12)))
 :qid |DafnyPre.1220:35|
 :skolemid |594|
 :no-pattern (type u@@12)
 :no-pattern (U_2_int u@@12)
 :no-pattern (U_2_bool u@@12)
)))) (=> (and (forall ((u@@13 T@U) ) (!  (=> (= (type u@@13) U@@18) (and (=> (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@13)) (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@13))) (=> (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@13)) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@13)))))
 :qid |DafnyPre.1219:35|
 :skolemid |593|
 :no-pattern (type u@@13)
 :no-pattern (U_2_int u@@13)
 :no-pattern (U_2_bool u@@13)
)) (forall ((u@@14 T@U) ) (!  (=> (and (= (type u@@14) U@@18) (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@14))) (= (MapType0Select (|Map#Elements| m@@19) u@@14) (MapType0Select (|Map#Elements| |m'|) u@@14)))
 :qid |DafnyPre.1220:35|
 :skolemid |594|
 :no-pattern (type u@@14)
 :no-pattern (U_2_int u@@14)
 :no-pattern (U_2_bool u@@14)
))) (|Map#Equal| m@@19 |m'|))))))
 :qid |DafnyPre.1217:21|
 :skolemid |595|
 :pattern ( (|Map#Equal| m@@19 |m'|))
)))
(assert (forall ((m@@20 T@U) (|m'@@0| T@U) ) (! (let ((V@@18 (MapTypeInv1 (type m@@20))))
(let ((U@@19 (MapTypeInv0 (type m@@20))))
 (=> (and (and (= (type m@@20) (MapType U@@19 V@@18)) (= (type |m'@@0|) (MapType U@@19 V@@18))) (|Map#Equal| m@@20 |m'@@0|)) (= m@@20 |m'@@0|))))
 :qid |DafnyPre.1222:21|
 :skolemid |596|
 :pattern ( (|Map#Equal| m@@20 |m'@@0|))
)))
(assert (forall ((m@@21 T@U) (|m'@@1| T@U) ) (! (let ((V@@19 (MapTypeInv1 (type m@@21))))
(let ((U@@20 (MapTypeInv0 (type m@@21))))
 (=> (and (= (type m@@21) (MapType U@@20 V@@19)) (= (type |m'@@1|) (MapType U@@20 V@@19))) (and (=> (|Map#Disjoint| m@@21 |m'@@1|) (forall ((o@@52 T@U) ) (!  (=> (= (type o@@52) U@@20) (or (not (U_2_bool (MapType0Select (|Map#Domain| m@@21) o@@52))) (not (U_2_bool (MapType0Select (|Map#Domain| |m'@@1|) o@@52)))))
 :qid |DafnyPre.1229:38|
 :skolemid |597|
 :pattern ( (MapType0Select (|Map#Domain| m@@21) o@@52))
 :pattern ( (MapType0Select (|Map#Domain| |m'@@1|) o@@52))
))) (=> (forall ((o@@53 T@U) ) (!  (=> (= (type o@@53) U@@20) (or (not (U_2_bool (MapType0Select (|Map#Domain| m@@21) o@@53))) (not (U_2_bool (MapType0Select (|Map#Domain| |m'@@1|) o@@53)))))
 :qid |DafnyPre.1229:38|
 :skolemid |597|
 :pattern ( (MapType0Select (|Map#Domain| m@@21) o@@53))
 :pattern ( (MapType0Select (|Map#Domain| |m'@@1|) o@@53))
)) (|Map#Disjoint| m@@21 |m'@@1|))))))
 :qid |DafnyPre.1227:21|
 :skolemid |598|
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
 :skolemid |599|
 :pattern ( (MapType0Select (|IMap#Domain| m@@22) u@@15))
 :pattern ( (MapType0Select (|IMap#Elements| m@@22) u@@15))
))) (=> (exists ((u@@16 T@U) ) (!  (and (= (type u@@16) U@@21) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@22) u@@16)) (= v@@42 (MapType0Select (|IMap#Elements| m@@22) u@@16))))
 :qid |DafnyPre.1252:10|
 :skolemid |599|
 :pattern ( (MapType0Select (|IMap#Domain| m@@22) u@@16))
 :pattern ( (MapType0Select (|IMap#Elements| m@@22) u@@16))
)) (U_2_bool (MapType0Select (|IMap#Values| m@@22) v@@42)))))))
 :qid |DafnyPre.1250:20|
 :skolemid |600|
 :pattern ( (MapType0Select (|IMap#Values| m@@22) v@@42))
)))
(assert (forall ((arg0@@104 T@U) ) (! (= (type (|IMap#Items| arg0@@104)) (MapType0Type BoxType boolType))
 :qid |funType:IMap#Items|
 :pattern ( (|IMap#Items| arg0@@104))
)))
(assert (forall ((m@@23 T@U) (item@@0 T@U) ) (!  (=> (and (= (type m@@23) (IMapType BoxType BoxType)) (= (type item@@0) BoxType)) (and (=> (U_2_bool (MapType0Select (|IMap#Items| m@@23) item@@0)) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select (|IMap#Elements| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0))))) (=> (and (U_2_bool (MapType0Select (|IMap#Domain| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select (|IMap#Elements| m@@23) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0)))) (U_2_bool (MapType0Select (|IMap#Items| m@@23) item@@0)))))
 :qid |DafnyPre.1267:15|
 :skolemid |601|
 :pattern ( (MapType0Select (|IMap#Items| m@@23) item@@0))
)))
(assert (forall ((U@@22 T@T) (V@@22 T@T) ) (! (= (type (|IMap#Empty| U@@22 V@@22)) (IMapType U@@22 V@@22))
 :qid |funType:IMap#Empty|
 :pattern ( (|IMap#Empty| U@@22 V@@22))
)))
(assert (forall ((u@@17 T@U) (V@@23 T@T) ) (! (let ((U@@23 (type u@@17)))
 (not (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Empty| U@@23 V@@23)) u@@17))))
 :qid |DafnyPre.1274:21|
 :skolemid |602|
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
 :skolemid |603|
 :pattern ( (|IMap#Domain| (|IMap#Glue| a@@76 b@@55 t@@32)))
)))
(assert (forall ((a@@77 T@U) (b@@56 T@U) (t@@33 T@U) ) (! (let ((V@@26 (MapType0TypeInv1 (type b@@56))))
(let ((U@@26 (MapType0TypeInv0 (type a@@77))))
 (=> (and (and (= (type a@@77) (MapType0Type U@@26 boolType)) (= (type b@@56) (MapType0Type U@@26 V@@26))) (= (type t@@33) TyType)) (= (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@33)) b@@56))))
 :qid |DafnyPre.1282:21|
 :skolemid |604|
 :pattern ( (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@33)))
)))
(assert (forall ((a@@78 T@U) (b@@57 T@U) (t@@34 T@U) ) (! (let ((V@@27 (MapType0TypeInv1 (type b@@57))))
(let ((U@@27 (MapType0TypeInv0 (type a@@78))))
 (=> (and (and (= (type a@@78) (MapType0Type U@@27 boolType)) (= (type b@@57) (MapType0Type U@@27 V@@27))) (= (type t@@34) TyType)) ($Is (|IMap#Glue| a@@78 b@@57 t@@34) t@@34))))
 :qid |DafnyPre.1285:21|
 :skolemid |605|
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
 :skolemid |606|
 :pattern ( (MapType0Select (|IMap#Domain| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|))
 :pattern ( (MapType0Select (|IMap#Elements| (|IMap#Build| m@@24 u@@18 v@@43)) |u'@@0|))
)))
(assert (forall ((m@@25 T@U) (|m'@@2| T@U) ) (! (let ((V@@30 (IMapTypeInv1 (type m@@25))))
(let ((U@@30 (IMapTypeInv0 (type m@@25))))
 (=> (and (= (type m@@25) (IMapType U@@30 V@@30)) (= (type |m'@@2|) (IMapType U@@30 V@@30))) (and (=> (|IMap#Equal| m@@25 |m'@@2|) (and (forall ((u@@19 T@U) ) (!  (=> (= (type u@@19) U@@30) (and (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@19)) (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@19))) (=> (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@19)) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@19)))))
 :qid |DafnyPre.1306:36|
 :skolemid |607|
 :no-pattern (type u@@19)
 :no-pattern (U_2_int u@@19)
 :no-pattern (U_2_bool u@@19)
)) (forall ((u@@20 T@U) ) (!  (=> (and (= (type u@@20) U@@30) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@20))) (= (MapType0Select (|IMap#Elements| m@@25) u@@20) (MapType0Select (|IMap#Elements| |m'@@2|) u@@20)))
 :qid |DafnyPre.1307:35|
 :skolemid |608|
 :no-pattern (type u@@20)
 :no-pattern (U_2_int u@@20)
 :no-pattern (U_2_bool u@@20)
)))) (=> (and (forall ((u@@21 T@U) ) (!  (=> (= (type u@@21) U@@30) (and (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@21)) (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@21))) (=> (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@21)) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@21)))))
 :qid |DafnyPre.1306:36|
 :skolemid |607|
 :no-pattern (type u@@21)
 :no-pattern (U_2_int u@@21)
 :no-pattern (U_2_bool u@@21)
)) (forall ((u@@22 T@U) ) (!  (=> (and (= (type u@@22) U@@30) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) u@@22))) (= (MapType0Select (|IMap#Elements| m@@25) u@@22) (MapType0Select (|IMap#Elements| |m'@@2|) u@@22)))
 :qid |DafnyPre.1307:35|
 :skolemid |608|
 :no-pattern (type u@@22)
 :no-pattern (U_2_int u@@22)
 :no-pattern (U_2_bool u@@22)
))) (|IMap#Equal| m@@25 |m'@@2|))))))
 :qid |DafnyPre.1304:21|
 :skolemid |609|
 :pattern ( (|IMap#Equal| m@@25 |m'@@2|))
)))
(assert (forall ((m@@26 T@U) (|m'@@3| T@U) ) (! (let ((V@@31 (IMapTypeInv1 (type m@@26))))
(let ((U@@31 (IMapTypeInv0 (type m@@26))))
 (=> (and (and (= (type m@@26) (IMapType U@@31 V@@31)) (= (type |m'@@3|) (IMapType U@@31 V@@31))) (|IMap#Equal| m@@26 |m'@@3|)) (= m@@26 |m'@@3|))))
 :qid |DafnyPre.1309:21|
 :skolemid |610|
 :pattern ( (|IMap#Equal| m@@26 |m'@@3|))
)))
(assert (forall ((x@@42 Int) (y@@12 Int) ) (! (= (INTERNAL_add_boogie x@@42 y@@12) (+ x@@42 y@@12))
 :qid |DafnyPre.1317:30|
 :skolemid |611|
 :pattern ( (INTERNAL_add_boogie x@@42 y@@12))
)))
(assert (forall ((x@@43 Int) (y@@13 Int) ) (! (= (INTERNAL_sub_boogie x@@43 y@@13) (- x@@43 y@@13))
 :qid |DafnyPre.1318:30|
 :skolemid |612|
 :pattern ( (INTERNAL_sub_boogie x@@43 y@@13))
)))
(assert (forall ((x@@44 Int) (y@@14 Int) ) (! (= (INTERNAL_mul_boogie x@@44 y@@14) (* x@@44 y@@14))
 :qid |DafnyPre.1319:30|
 :skolemid |613|
 :pattern ( (INTERNAL_mul_boogie x@@44 y@@14))
)))
(assert (forall ((x@@45 Int) (y@@15 Int) ) (! (= (INTERNAL_div_boogie x@@45 y@@15) (div x@@45 y@@15))
 :qid |DafnyPre.1320:30|
 :skolemid |614|
 :pattern ( (INTERNAL_div_boogie x@@45 y@@15))
)))
(assert (forall ((x@@46 Int) (y@@16 Int) ) (! (= (INTERNAL_mod_boogie x@@46 y@@16) (mod x@@46 y@@16))
 :qid |DafnyPre.1321:30|
 :skolemid |615|
 :pattern ( (INTERNAL_mod_boogie x@@46 y@@16))
)))
(assert (forall ((x@@47 Int) (y@@17 Int) ) (!  (and (=> (INTERNAL_lt_boogie x@@47 y@@17) (< x@@47 y@@17)) (=> (< x@@47 y@@17) (INTERNAL_lt_boogie x@@47 y@@17)))
 :qid |DafnyPre.1322:51|
 :skolemid |616|
 :pattern ( (INTERNAL_lt_boogie x@@47 y@@17))
)))
(assert (forall ((x@@48 Int) (y@@18 Int) ) (!  (and (=> (INTERNAL_le_boogie x@@48 y@@18) (<= x@@48 y@@18)) (=> (<= x@@48 y@@18) (INTERNAL_le_boogie x@@48 y@@18)))
 :qid |DafnyPre.1323:51|
 :skolemid |617|
 :pattern ( (INTERNAL_le_boogie x@@48 y@@18))
)))
(assert (forall ((x@@49 Int) (y@@19 Int) ) (!  (and (=> (INTERNAL_gt_boogie x@@49 y@@19) (> x@@49 y@@19)) (=> (> x@@49 y@@19) (INTERNAL_gt_boogie x@@49 y@@19)))
 :qid |DafnyPre.1324:51|
 :skolemid |618|
 :pattern ( (INTERNAL_gt_boogie x@@49 y@@19))
)))
(assert (forall ((x@@50 Int) (y@@20 Int) ) (!  (and (=> (INTERNAL_ge_boogie x@@50 y@@20) (>= x@@50 y@@20)) (=> (>= x@@50 y@@20) (INTERNAL_ge_boogie x@@50 y@@20)))
 :qid |DafnyPre.1325:51|
 :skolemid |619|
 :pattern ( (INTERNAL_ge_boogie x@@50 y@@20))
)))
(assert (= (type Tclass._System.nat) TyType))
(assert (= (Tag Tclass._System.nat) Tagclass._System.nat))
(assert (forall ((bx@@34 T@U) ) (!  (=> (and (= (type bx@@34) BoxType) ($IsBox bx@@34 Tclass._System.nat)) (and (= ($Box ($Unbox intType bx@@34)) bx@@34) ($Is ($Unbox intType bx@@34) Tclass._System.nat)))
 :qid |unknown.0:0|
 :skolemid |620|
 :pattern ( ($IsBox bx@@34 Tclass._System.nat))
)))
(assert (forall ((|x#0| T@U) ) (!  (=> (= (type |x#0|) intType) (and (=> ($Is |x#0| Tclass._System.nat) (<= 0 (U_2_int |x#0|))) (=> (<= 0 (U_2_int |x#0|)) ($Is |x#0| Tclass._System.nat))))
 :qid |unknown.0:0|
 :skolemid |621|
 :pattern ( ($Is |x#0| Tclass._System.nat))
)))
(assert (forall ((|x#0@@0| T@U) ($h T@U) ) (!  (=> (and (= (type |x#0@@0|) intType) (= (type $h) (MapType0Type refType MapType1Type))) ($IsAlloc |x#0@@0| Tclass._System.nat $h))
 :qid |unknown.0:0|
 :skolemid |622|
 :pattern ( ($IsAlloc |x#0@@0| Tclass._System.nat $h))
)))
(assert (= (Tag Tclass._System.object?) Tagclass._System.object?))
(assert (forall ((bx@@35 T@U) ) (!  (=> (and (= (type bx@@35) BoxType) ($IsBox bx@@35 Tclass._System.object?)) (and (= ($Box ($Unbox refType bx@@35)) bx@@35) ($Is ($Unbox refType bx@@35) Tclass._System.object?)))
 :qid |unknown.0:0|
 :skolemid |623|
 :pattern ( ($IsBox bx@@35 Tclass._System.object?))
)))
(assert (forall (($o T@U) ) (!  (=> (= (type $o) refType) ($Is $o Tclass._System.object?))
 :qid |unknown.0:0|
 :skolemid |624|
 :pattern ( ($Is $o Tclass._System.object?))
)))
(assert (= (type null) refType))
(assert (forall (($o@@0 T@U) ($h@@0 T@U) ) (!  (=> (and (= (type $o@@0) refType) (= (type $h@@0) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc $o@@0 Tclass._System.object? $h@@0) (or (= $o@@0 null) (U_2_bool (MapType1Select (MapType0Select $h@@0 $o@@0) alloc)))) (=> (or (= $o@@0 null) (U_2_bool (MapType1Select (MapType0Select $h@@0 $o@@0) alloc))) ($IsAlloc $o@@0 Tclass._System.object? $h@@0))))
 :qid |unknown.0:0|
 :skolemid |625|
 :pattern ( ($IsAlloc $o@@0 Tclass._System.object? $h@@0))
)))
(assert (= (type Tclass._System.object) TyType))
(assert (= (Tag Tclass._System.object) Tagclass._System.object))
(assert (forall ((bx@@36 T@U) ) (!  (=> (and (= (type bx@@36) BoxType) ($IsBox bx@@36 Tclass._System.object)) (and (= ($Box ($Unbox refType bx@@36)) bx@@36) ($Is ($Unbox refType bx@@36) Tclass._System.object)))
 :qid |unknown.0:0|
 :skolemid |626|
 :pattern ( ($IsBox bx@@36 Tclass._System.object))
)))
(assert (forall ((|c#0| T@U) ) (!  (=> (= (type |c#0|) refType) (and (=> ($Is |c#0| Tclass._System.object) (and ($Is |c#0| Tclass._System.object?) (not (= |c#0| null)))) (=> (and ($Is |c#0| Tclass._System.object?) (not (= |c#0| null))) ($Is |c#0| Tclass._System.object))))
 :qid |unknown.0:0|
 :skolemid |627|
 :pattern ( ($Is |c#0| Tclass._System.object))
)))
(assert (forall ((|c#0@@0| T@U) ($h@@1 T@U) ) (!  (=> (and (= (type |c#0@@0|) refType) (= (type $h@@1) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |c#0@@0| Tclass._System.object $h@@1) ($IsAlloc |c#0@@0| Tclass._System.object? $h@@1)) (=> ($IsAlloc |c#0@@0| Tclass._System.object? $h@@1) ($IsAlloc |c#0@@0| Tclass._System.object $h@@1))))
 :qid |unknown.0:0|
 :skolemid |628|
 :pattern ( ($IsAlloc |c#0@@0| Tclass._System.object $h@@1))
)))
(assert (forall ((arg0@@107 T@U) ) (! (= (type (Tclass._System.array? arg0@@107)) TyType)
 :qid |funType:Tclass._System.array?|
 :pattern ( (Tclass._System.array? arg0@@107))
)))
(assert (forall ((|#$arg| T@U) ) (!  (=> (= (type |#$arg|) TyType) (= (Tag (Tclass._System.array? |#$arg|)) Tagclass._System.array?))
 :qid |unknown.0:0|
 :skolemid |629|
 :pattern ( (Tclass._System.array? |#$arg|))
)))
(assert (forall ((arg0@@108 T@U) ) (! (= (type (Tclass._System.array?_0 arg0@@108)) TyType)
 :qid |funType:Tclass._System.array?_0|
 :pattern ( (Tclass._System.array?_0 arg0@@108))
)))
(assert (forall ((|#$arg@@0| T@U) ) (!  (=> (= (type |#$arg@@0|) TyType) (= (Tclass._System.array?_0 (Tclass._System.array? |#$arg@@0|)) |#$arg@@0|))
 :qid |unknown.0:0|
 :skolemid |630|
 :pattern ( (Tclass._System.array? |#$arg@@0|))
)))
(assert (forall ((|#$arg@@1| T@U) (bx@@37 T@U) ) (!  (=> (and (and (= (type |#$arg@@1|) TyType) (= (type bx@@37) BoxType)) ($IsBox bx@@37 (Tclass._System.array? |#$arg@@1|))) (and (= ($Box ($Unbox refType bx@@37)) bx@@37) ($Is ($Unbox refType bx@@37) (Tclass._System.array? |#$arg@@1|))))
 :qid |unknown.0:0|
 :skolemid |631|
 :pattern ( ($IsBox bx@@37 (Tclass._System.array? |#$arg@@1|)))
)))
(assert (forall ((arg0@@109 T@U) ) (! (= (type (dtype arg0@@109)) TyType)
 :qid |funType:dtype|
 :pattern ( (dtype arg0@@109))
)))
(assert (forall ((|#$arg@@2| T@U) ($h@@2 T@U) ($o@@1 T@U) ($i0 Int) ) (!  (=> (and (and (and (= (type |#$arg@@2|) TyType) (= (type $h@@2) (MapType0Type refType MapType1Type))) (= (type $o@@1) refType)) (and (and ($IsGoodHeap $h@@2) (and (not (= $o@@1 null)) (= (dtype $o@@1) (Tclass._System.array? |#$arg@@2|)))) (and (<= 0 $i0) (< $i0 (_System.array.Length $o@@1))))) ($IsBox (MapType1Select (MapType0Select $h@@2 $o@@1) (IndexField $i0)) |#$arg@@2|))
 :qid |unknown.0:0|
 :skolemid |632|
 :pattern ( (MapType1Select (MapType0Select $h@@2 $o@@1) (IndexField $i0)) (Tclass._System.array? |#$arg@@2|))
)))
(assert (forall ((|#$arg@@3| T@U) ($h@@3 T@U) ($o@@2 T@U) ($i0@@0 Int) ) (!  (=> (and (and (= (type |#$arg@@3|) TyType) (= (type $h@@3) (MapType0Type refType MapType1Type))) (= (type $o@@2) refType)) (=> (and (and (and ($IsGoodHeap $h@@3) (and (not (= $o@@2 null)) (= (dtype $o@@2) (Tclass._System.array? |#$arg@@3|)))) (and (<= 0 $i0@@0) (< $i0@@0 (_System.array.Length $o@@2)))) (U_2_bool (MapType1Select (MapType0Select $h@@3 $o@@2) alloc))) ($IsAllocBox (MapType1Select (MapType0Select $h@@3 $o@@2) (IndexField $i0@@0)) |#$arg@@3| $h@@3)))
 :qid |unknown.0:0|
 :skolemid |633|
 :pattern ( (MapType1Select (MapType0Select $h@@3 $o@@2) (IndexField $i0@@0)) (Tclass._System.array? |#$arg@@3|))
)))
(assert (forall ((|#$arg@@4| T@U) ($o@@3 T@U) ) (!  (=> (and (= (type |#$arg@@4|) TyType) (= (type $o@@3) refType)) (and (=> ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)) (or (= $o@@3 null) (= (dtype $o@@3) (Tclass._System.array? |#$arg@@4|)))) (=> (or (= $o@@3 null) (= (dtype $o@@3) (Tclass._System.array? |#$arg@@4|))) ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)))))
 :qid |unknown.0:0|
 :skolemid |634|
 :pattern ( ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)))
)))
(assert (forall ((|#$arg@@5| T@U) ($o@@4 T@U) ($h@@4 T@U) ) (!  (=> (and (and (= (type |#$arg@@5|) TyType) (= (type $o@@4) refType)) (= (type $h@@4) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4) (or (= $o@@4 null) (U_2_bool (MapType1Select (MapType0Select $h@@4 $o@@4) alloc)))) (=> (or (= $o@@4 null) (U_2_bool (MapType1Select (MapType0Select $h@@4 $o@@4) alloc))) ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4))))
 :qid |unknown.0:0|
 :skolemid |635|
 :pattern ( ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4))
)))
(assert (forall ((|#$arg@@6| T@U) ($o@@5 T@U) ) (!  (=> (and (and (= (type |#$arg@@6|) TyType) (= (type $o@@5) refType)) (and (not (= $o@@5 null)) (= (dtype $o@@5) (Tclass._System.array? |#$arg@@6|)))) ($Is (int_2_U (_System.array.Length $o@@5)) TInt))
 :qid |unknown.0:0|
 :skolemid |636|
 :pattern ( (_System.array.Length $o@@5) (Tclass._System.array? |#$arg@@6|))
)))
(assert (forall ((|#$arg@@7| T@U) ($h@@5 T@U) ($o@@6 T@U) ) (!  (=> (and (and (and (= (type |#$arg@@7|) TyType) (= (type $h@@5) (MapType0Type refType MapType1Type))) (= (type $o@@6) refType)) (and (and ($IsGoodHeap $h@@5) (and (not (= $o@@6 null)) (= (dtype $o@@6) (Tclass._System.array? |#$arg@@7|)))) (U_2_bool (MapType1Select (MapType0Select $h@@5 $o@@6) alloc)))) ($IsAlloc (int_2_U (_System.array.Length $o@@6)) TInt $h@@5))
 :qid |unknown.0:0|
 :skolemid |637|
 :pattern ( (_System.array.Length $o@@6) (MapType1Select (MapType0Select $h@@5 $o@@6) alloc) (Tclass._System.array? |#$arg@@7|))
)))
(assert (forall ((arg0@@110 T@U) ) (! (= (type (Tclass._System.array arg0@@110)) TyType)
 :qid |funType:Tclass._System.array|
 :pattern ( (Tclass._System.array arg0@@110))
)))
(assert (forall ((_System.array$arg T@U) ) (!  (=> (= (type _System.array$arg) TyType) (= (Tag (Tclass._System.array _System.array$arg)) Tagclass._System.array))
 :qid |unknown.0:0|
 :skolemid |638|
 :pattern ( (Tclass._System.array _System.array$arg))
)))
(assert (forall ((arg0@@111 T@U) ) (! (= (type (Tclass._System.array_0 arg0@@111)) TyType)
 :qid |funType:Tclass._System.array_0|
 :pattern ( (Tclass._System.array_0 arg0@@111))
)))
(assert (forall ((_System.array$arg@@0 T@U) ) (!  (=> (= (type _System.array$arg@@0) TyType) (= (Tclass._System.array_0 (Tclass._System.array _System.array$arg@@0)) _System.array$arg@@0))
 :qid |unknown.0:0|
 :skolemid |639|
 :pattern ( (Tclass._System.array _System.array$arg@@0))
)))
(assert (forall ((_System.array$arg@@1 T@U) (bx@@38 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@1) TyType) (= (type bx@@38) BoxType)) ($IsBox bx@@38 (Tclass._System.array _System.array$arg@@1))) (and (= ($Box ($Unbox refType bx@@38)) bx@@38) ($Is ($Unbox refType bx@@38) (Tclass._System.array _System.array$arg@@1))))
 :qid |unknown.0:0|
 :skolemid |640|
 :pattern ( ($IsBox bx@@38 (Tclass._System.array _System.array$arg@@1)))
)))
(assert (forall ((_System.array$arg@@2 T@U) (|c#0@@1| T@U) ) (!  (=> (and (= (type _System.array$arg@@2) TyType) (= (type |c#0@@1|) refType)) (and (=> ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)) (and ($Is |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (not (= |c#0@@1| null)))) (=> (and ($Is |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (not (= |c#0@@1| null))) ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)))))
 :qid |unknown.0:0|
 :skolemid |641|
 :pattern ( ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)))
)))
(assert (forall ((_System.array$arg@@3 T@U) (|c#0@@2| T@U) ($h@@6 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@3) TyType) (= (type |c#0@@2|) refType)) (= (type $h@@6) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6) ($IsAlloc |c#0@@2| (Tclass._System.array? _System.array$arg@@3) $h@@6)) (=> ($IsAlloc |c#0@@2| (Tclass._System.array? _System.array$arg@@3) $h@@6) ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6))))
 :qid |unknown.0:0|
 :skolemid |642|
 :pattern ( ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6))
)))
(assert (forall ((arg0@@112 T@U) (arg1@@47 T@U) ) (! (= (type (Tclass._System.___hFunc1 arg0@@112 arg1@@47)) TyType)
 :qid |funType:Tclass._System.___hFunc1|
 :pattern ( (Tclass._System.___hFunc1 arg0@@112 arg1@@47))
)))
(assert (forall ((|#$T0| T@U) (|#$R| T@U) ) (!  (=> (and (= (type |#$T0|) TyType) (= (type |#$R|) TyType)) (= (Tag (Tclass._System.___hFunc1 |#$T0| |#$R|)) Tagclass._System.___hFunc1))
 :qid |unknown.0:0|
 :skolemid |643|
 :pattern ( (Tclass._System.___hFunc1 |#$T0| |#$R|))
)))
(assert (forall ((arg0@@113 T@U) ) (! (= (type (Tclass._System.___hFunc1_0 arg0@@113)) TyType)
 :qid |funType:Tclass._System.___hFunc1_0|
 :pattern ( (Tclass._System.___hFunc1_0 arg0@@113))
)))
(assert (forall ((|#$T0@@0| T@U) (|#$R@@0| T@U) ) (!  (=> (and (= (type |#$T0@@0|) TyType) (= (type |#$R@@0|) TyType)) (= (Tclass._System.___hFunc1_0 (Tclass._System.___hFunc1 |#$T0@@0| |#$R@@0|)) |#$T0@@0|))
 :qid |unknown.0:0|
 :skolemid |644|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@0| |#$R@@0|))
)))
(assert (forall ((arg0@@114 T@U) ) (! (= (type (Tclass._System.___hFunc1_1 arg0@@114)) TyType)
 :qid |funType:Tclass._System.___hFunc1_1|
 :pattern ( (Tclass._System.___hFunc1_1 arg0@@114))
)))
(assert (forall ((|#$T0@@1| T@U) (|#$R@@1| T@U) ) (!  (=> (and (= (type |#$T0@@1|) TyType) (= (type |#$R@@1|) TyType)) (= (Tclass._System.___hFunc1_1 (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@1|)) |#$R@@1|))
 :qid |unknown.0:0|
 :skolemid |645|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@1|))
)))
(assert (forall ((|#$T0@@2| T@U) (|#$R@@2| T@U) (bx@@39 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@2|) TyType) (= (type |#$R@@2|) TyType)) (= (type bx@@39) BoxType)) ($IsBox bx@@39 (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|))) (and (= ($Box ($Unbox HandleTypeType bx@@39)) bx@@39) ($Is ($Unbox HandleTypeType bx@@39) (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|))))
 :qid |unknown.0:0|
 :skolemid |646|
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
 :skolemid |647|
 :pattern ( (Apply1 t0@@12 t1@@3 heap@@1 (Handle1 h@@20 r@@6 rd) bx0))
)))
(assert (forall ((t0@@13 T@U) (t1@@4 T@U) (heap@@2 T@U) (h@@21 T@U) (r@@7 T@U) (rd@@0 T@U) (bx0@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@13) TyType) (= (type t1@@4) TyType)) (= (type heap@@2) (MapType0Type refType MapType1Type))) (= (type h@@21) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@7) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd@@0) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@0) BoxType)) (U_2_bool (MapType2Select r@@7 heap@@2 bx0@@0))) (Requires1 t0@@13 t1@@4 heap@@2 (Handle1 h@@21 r@@7 rd@@0) bx0@@0))
 :qid |unknown.0:0|
 :skolemid |648|
 :pattern ( (Requires1 t0@@13 t1@@4 heap@@2 (Handle1 h@@21 r@@7 rd@@0) bx0@@0))
)))
(assert (forall ((arg0@@122 T@U) (arg1@@55 T@U) (arg2@@15 T@U) (arg3@@2 T@U) (arg4@@0 T@U) ) (! (= (type (Reads1 arg0@@122 arg1@@55 arg2@@15 arg3@@2 arg4@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads1|
 :pattern ( (Reads1 arg0@@122 arg1@@55 arg2@@15 arg3@@2 arg4@@0))
)))
(assert (forall ((t0@@14 T@U) (t1@@5 T@U) (heap@@3 T@U) (h@@22 T@U) (r@@8 T@U) (rd@@1 T@U) (bx0@@1 T@U) (bx@@40 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@14) TyType) (= (type t1@@5) TyType)) (= (type heap@@3) (MapType0Type refType MapType1Type))) (= (type h@@22) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@8) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd@@1) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@1) BoxType)) (= (type bx@@40) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads1 t0@@14 t1@@5 heap@@3 (Handle1 h@@22 r@@8 rd@@1) bx0@@1) bx@@40)) (U_2_bool (MapType0Select (MapType2Select rd@@1 heap@@3 bx0@@1) bx@@40))) (=> (U_2_bool (MapType0Select (MapType2Select rd@@1 heap@@3 bx0@@1) bx@@40)) (U_2_bool (MapType0Select (Reads1 t0@@14 t1@@5 heap@@3 (Handle1 h@@22 r@@8 rd@@1) bx0@@1) bx@@40)))))
 :qid |unknown.0:0|
 :skolemid |649|
 :pattern ( (MapType0Select (Reads1 t0@@14 t1@@5 heap@@3 (Handle1 h@@22 r@@8 rd@@1) bx0@@1) bx@@40))
)))
(assert (forall ((t0@@15 T@U) (t1@@6 T@U) (h0@@0 T@U) (h1@@0 T@U) (f@@5 T@U) (bx0@@2 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@15) TyType) (= (type t1@@6) TyType)) (= (type h0@@0) (MapType0Type refType MapType1Type))) (= (type h1@@0) (MapType0Type refType MapType1Type))) (= (type f@@5) HandleTypeType)) (= (type bx0@@2) BoxType)) (and (and (and ($HeapSucc h0@@0 h1@@0) (and ($IsGoodHeap h0@@0) ($IsGoodHeap h1@@0))) (and ($IsBox bx0@@2 t0@@15) ($Is f@@5 (Tclass._System.___hFunc1 t0@@15 t1@@6)))) (forall ((o@@54 T@U) (fld T@U) ) (! (let ((a@@79 (FieldTypeInv0 (type fld))))
 (=> (and (and (= (type o@@54) refType) (= (type fld) (FieldType a@@79))) (and (not (= o@@54 null)) (U_2_bool (MapType0Select (Reads1 t0@@15 t1@@6 h0@@0 f@@5 bx0@@2) ($Box o@@54))))) (= (MapType1Select (MapType0Select h0@@0 o@@54) fld) (MapType1Select (MapType0Select h1@@0 o@@54) fld))))
 :qid |unknown.0:0|
 :skolemid |650|
 :no-pattern (type o@@54)
 :no-pattern (type fld)
 :no-pattern (U_2_int o@@54)
 :no-pattern (U_2_bool o@@54)
 :no-pattern (U_2_int fld)
 :no-pattern (U_2_bool fld)
)))) (= (Reads1 t0@@15 t1@@6 h0@@0 f@@5 bx0@@2) (Reads1 t0@@15 t1@@6 h1@@0 f@@5 bx0@@2)))
 :qid |unknown.0:0|
 :skolemid |651|
 :pattern ( ($HeapSucc h0@@0 h1@@0) (Reads1 t0@@15 t1@@6 h1@@0 f@@5 bx0@@2))
)))
(assert (forall ((t0@@16 T@U) (t1@@7 T@U) (h0@@1 T@U) (h1@@1 T@U) (f@@6 T@U) (bx0@@3 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@16) TyType) (= (type t1@@7) TyType)) (= (type h0@@1) (MapType0Type refType MapType1Type))) (= (type h1@@1) (MapType0Type refType MapType1Type))) (= (type f@@6) HandleTypeType)) (= (type bx0@@3) BoxType)) (and (and (and ($HeapSucc h0@@1 h1@@1) (and ($IsGoodHeap h0@@1) ($IsGoodHeap h1@@1))) (and ($IsBox bx0@@3 t0@@16) ($Is f@@6 (Tclass._System.___hFunc1 t0@@16 t1@@7)))) (forall ((o@@55 T@U) (fld@@0 T@U) ) (! (let ((a@@80 (FieldTypeInv0 (type fld@@0))))
 (=> (and (and (= (type o@@55) refType) (= (type fld@@0) (FieldType a@@80))) (and (not (= o@@55 null)) (U_2_bool (MapType0Select (Reads1 t0@@16 t1@@7 h1@@1 f@@6 bx0@@3) ($Box o@@55))))) (= (MapType1Select (MapType0Select h0@@1 o@@55) fld@@0) (MapType1Select (MapType0Select h1@@1 o@@55) fld@@0))))
 :qid |unknown.0:0|
 :skolemid |652|
 :no-pattern (type o@@55)
 :no-pattern (type fld@@0)
 :no-pattern (U_2_int o@@55)
 :no-pattern (U_2_bool o@@55)
 :no-pattern (U_2_int fld@@0)
 :no-pattern (U_2_bool fld@@0)
)))) (= (Reads1 t0@@16 t1@@7 h0@@1 f@@6 bx0@@3) (Reads1 t0@@16 t1@@7 h1@@1 f@@6 bx0@@3)))
 :qid |unknown.0:0|
 :skolemid |653|
 :pattern ( ($HeapSucc h0@@1 h1@@1) (Reads1 t0@@16 t1@@7 h1@@1 f@@6 bx0@@3))
)))
(assert (forall ((t0@@17 T@U) (t1@@8 T@U) (h0@@2 T@U) (h1@@2 T@U) (f@@7 T@U) (bx0@@4 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@17) TyType) (= (type t1@@8) TyType)) (= (type h0@@2) (MapType0Type refType MapType1Type))) (= (type h1@@2) (MapType0Type refType MapType1Type))) (= (type f@@7) HandleTypeType)) (= (type bx0@@4) BoxType)) (and (and (and ($HeapSucc h0@@2 h1@@2) (and ($IsGoodHeap h0@@2) ($IsGoodHeap h1@@2))) (and ($IsBox bx0@@4 t0@@17) ($Is f@@7 (Tclass._System.___hFunc1 t0@@17 t1@@8)))) (forall ((o@@56 T@U) (fld@@1 T@U) ) (! (let ((a@@81 (FieldTypeInv0 (type fld@@1))))
 (=> (and (and (= (type o@@56) refType) (= (type fld@@1) (FieldType a@@81))) (and (not (= o@@56 null)) (U_2_bool (MapType0Select (Reads1 t0@@17 t1@@8 h0@@2 f@@7 bx0@@4) ($Box o@@56))))) (= (MapType1Select (MapType0Select h0@@2 o@@56) fld@@1) (MapType1Select (MapType0Select h1@@2 o@@56) fld@@1))))
 :qid |unknown.0:0|
 :skolemid |654|
 :no-pattern (type o@@56)
 :no-pattern (type fld@@1)
 :no-pattern (U_2_int o@@56)
 :no-pattern (U_2_bool o@@56)
 :no-pattern (U_2_int fld@@1)
 :no-pattern (U_2_bool fld@@1)
)))) (and (=> (Requires1 t0@@17 t1@@8 h0@@2 f@@7 bx0@@4) (Requires1 t0@@17 t1@@8 h1@@2 f@@7 bx0@@4)) (=> (Requires1 t0@@17 t1@@8 h1@@2 f@@7 bx0@@4) (Requires1 t0@@17 t1@@8 h0@@2 f@@7 bx0@@4))))
 :qid |unknown.0:0|
 :skolemid |655|
 :pattern ( ($HeapSucc h0@@2 h1@@2) (Requires1 t0@@17 t1@@8 h1@@2 f@@7 bx0@@4))
)))
(assert (forall ((t0@@18 T@U) (t1@@9 T@U) (h0@@3 T@U) (h1@@3 T@U) (f@@8 T@U) (bx0@@5 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@18) TyType) (= (type t1@@9) TyType)) (= (type h0@@3) (MapType0Type refType MapType1Type))) (= (type h1@@3) (MapType0Type refType MapType1Type))) (= (type f@@8) HandleTypeType)) (= (type bx0@@5) BoxType)) (and (and (and ($HeapSucc h0@@3 h1@@3) (and ($IsGoodHeap h0@@3) ($IsGoodHeap h1@@3))) (and ($IsBox bx0@@5 t0@@18) ($Is f@@8 (Tclass._System.___hFunc1 t0@@18 t1@@9)))) (forall ((o@@57 T@U) (fld@@2 T@U) ) (! (let ((a@@82 (FieldTypeInv0 (type fld@@2))))
 (=> (and (and (= (type o@@57) refType) (= (type fld@@2) (FieldType a@@82))) (and (not (= o@@57 null)) (U_2_bool (MapType0Select (Reads1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5) ($Box o@@57))))) (= (MapType1Select (MapType0Select h0@@3 o@@57) fld@@2) (MapType1Select (MapType0Select h1@@3 o@@57) fld@@2))))
 :qid |unknown.0:0|
 :skolemid |656|
 :no-pattern (type o@@57)
 :no-pattern (type fld@@2)
 :no-pattern (U_2_int o@@57)
 :no-pattern (U_2_bool o@@57)
 :no-pattern (U_2_int fld@@2)
 :no-pattern (U_2_bool fld@@2)
)))) (and (=> (Requires1 t0@@18 t1@@9 h0@@3 f@@8 bx0@@5) (Requires1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5)) (=> (Requires1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5) (Requires1 t0@@18 t1@@9 h0@@3 f@@8 bx0@@5))))
 :qid |unknown.0:0|
 :skolemid |657|
 :pattern ( ($HeapSucc h0@@3 h1@@3) (Requires1 t0@@18 t1@@9 h1@@3 f@@8 bx0@@5))
)))
(assert (forall ((t0@@19 T@U) (t1@@10 T@U) (h0@@4 T@U) (h1@@4 T@U) (f@@9 T@U) (bx0@@6 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@19) TyType) (= (type t1@@10) TyType)) (= (type h0@@4) (MapType0Type refType MapType1Type))) (= (type h1@@4) (MapType0Type refType MapType1Type))) (= (type f@@9) HandleTypeType)) (= (type bx0@@6) BoxType)) (and (and (and ($HeapSucc h0@@4 h1@@4) (and ($IsGoodHeap h0@@4) ($IsGoodHeap h1@@4))) (and ($IsBox bx0@@6 t0@@19) ($Is f@@9 (Tclass._System.___hFunc1 t0@@19 t1@@10)))) (forall ((o@@58 T@U) (fld@@3 T@U) ) (! (let ((a@@83 (FieldTypeInv0 (type fld@@3))))
 (=> (and (and (= (type o@@58) refType) (= (type fld@@3) (FieldType a@@83))) (and (not (= o@@58 null)) (U_2_bool (MapType0Select (Reads1 t0@@19 t1@@10 h0@@4 f@@9 bx0@@6) ($Box o@@58))))) (= (MapType1Select (MapType0Select h0@@4 o@@58) fld@@3) (MapType1Select (MapType0Select h1@@4 o@@58) fld@@3))))
 :qid |unknown.0:0|
 :skolemid |658|
 :no-pattern (type o@@58)
 :no-pattern (type fld@@3)
 :no-pattern (U_2_int o@@58)
 :no-pattern (U_2_bool o@@58)
 :no-pattern (U_2_int fld@@3)
 :no-pattern (U_2_bool fld@@3)
)))) (= (Apply1 t0@@19 t1@@10 h0@@4 f@@9 bx0@@6) (Apply1 t0@@19 t1@@10 h1@@4 f@@9 bx0@@6)))
 :qid |unknown.0:0|
 :skolemid |659|
 :pattern ( ($HeapSucc h0@@4 h1@@4) (Apply1 t0@@19 t1@@10 h1@@4 f@@9 bx0@@6))
)))
(assert (forall ((t0@@20 T@U) (t1@@11 T@U) (h0@@5 T@U) (h1@@5 T@U) (f@@10 T@U) (bx0@@7 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@20) TyType) (= (type t1@@11) TyType)) (= (type h0@@5) (MapType0Type refType MapType1Type))) (= (type h1@@5) (MapType0Type refType MapType1Type))) (= (type f@@10) HandleTypeType)) (= (type bx0@@7) BoxType)) (and (and (and ($HeapSucc h0@@5 h1@@5) (and ($IsGoodHeap h0@@5) ($IsGoodHeap h1@@5))) (and ($IsBox bx0@@7 t0@@20) ($Is f@@10 (Tclass._System.___hFunc1 t0@@20 t1@@11)))) (forall ((o@@59 T@U) (fld@@4 T@U) ) (! (let ((a@@84 (FieldTypeInv0 (type fld@@4))))
 (=> (and (and (= (type o@@59) refType) (= (type fld@@4) (FieldType a@@84))) (and (not (= o@@59 null)) (U_2_bool (MapType0Select (Reads1 t0@@20 t1@@11 h1@@5 f@@10 bx0@@7) ($Box o@@59))))) (= (MapType1Select (MapType0Select h0@@5 o@@59) fld@@4) (MapType1Select (MapType0Select h1@@5 o@@59) fld@@4))))
 :qid |unknown.0:0|
 :skolemid |660|
 :no-pattern (type o@@59)
 :no-pattern (type fld@@4)
 :no-pattern (U_2_int o@@59)
 :no-pattern (U_2_bool o@@59)
 :no-pattern (U_2_int fld@@4)
 :no-pattern (U_2_bool fld@@4)
)))) (= (Apply1 t0@@20 t1@@11 h0@@5 f@@10 bx0@@7) (Apply1 t0@@20 t1@@11 h1@@5 f@@10 bx0@@7)))
 :qid |unknown.0:0|
 :skolemid |661|
 :pattern ( ($HeapSucc h0@@5 h1@@5) (Apply1 t0@@20 t1@@11 h1@@5 f@@10 bx0@@7))
)))
(assert (forall ((t0@@21 T@U) (t1@@12 T@U) (heap@@4 T@U) (f@@11 T@U) (bx0@@8 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@21) TyType) (= (type t1@@12) TyType)) (= (type heap@@4) (MapType0Type refType MapType1Type))) (= (type f@@11) HandleTypeType)) (= (type bx0@@8) BoxType)) (and ($IsGoodHeap heap@@4) (and ($IsBox bx0@@8 t0@@21) ($Is f@@11 (Tclass._System.___hFunc1 t0@@21 t1@@12))))) (and (=> (|Set#Equal| (Reads1 t0@@21 t1@@12 $OneHeap f@@11 bx0@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads1 t0@@21 t1@@12 heap@@4 f@@11 bx0@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads1 t0@@21 t1@@12 heap@@4 f@@11 bx0@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads1 t0@@21 t1@@12 $OneHeap f@@11 bx0@@8) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |662|
 :pattern ( (Reads1 t0@@21 t1@@12 $OneHeap f@@11 bx0@@8) ($IsGoodHeap heap@@4))
 :pattern ( (Reads1 t0@@21 t1@@12 heap@@4 f@@11 bx0@@8))
)))
(assert (forall ((t0@@22 T@U) (t1@@13 T@U) (heap@@5 T@U) (f@@12 T@U) (bx0@@9 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@22) TyType) (= (type t1@@13) TyType)) (= (type heap@@5) (MapType0Type refType MapType1Type))) (= (type f@@12) HandleTypeType)) (= (type bx0@@9) BoxType)) (and (and ($IsGoodHeap heap@@5) (and ($IsBox bx0@@9 t0@@22) ($Is f@@12 (Tclass._System.___hFunc1 t0@@22 t1@@13)))) (|Set#Equal| (Reads1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9) (|Set#Empty| BoxType)))) (and (=> (Requires1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9) (Requires1 t0@@22 t1@@13 heap@@5 f@@12 bx0@@9)) (=> (Requires1 t0@@22 t1@@13 heap@@5 f@@12 bx0@@9) (Requires1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9))))
 :qid |unknown.0:0|
 :skolemid |663|
 :pattern ( (Requires1 t0@@22 t1@@13 $OneHeap f@@12 bx0@@9) ($IsGoodHeap heap@@5))
 :pattern ( (Requires1 t0@@22 t1@@13 heap@@5 f@@12 bx0@@9))
)))
(assert (forall ((f@@13 T@U) (t0@@23 T@U) (t1@@14 T@U) ) (!  (=> (and (and (= (type f@@13) HandleTypeType) (= (type t0@@23) TyType)) (= (type t1@@14) TyType)) (and (=> ($Is f@@13 (Tclass._System.___hFunc1 t0@@23 t1@@14)) (forall ((h@@23 T@U) (bx0@@10 T@U) ) (!  (=> (and (= (type h@@23) (MapType0Type refType MapType1Type)) (= (type bx0@@10) BoxType)) (=> (and (and ($IsGoodHeap h@@23) ($IsBox bx0@@10 t0@@23)) (Requires1 t0@@23 t1@@14 h@@23 f@@13 bx0@@10)) ($IsBox (Apply1 t0@@23 t1@@14 h@@23 f@@13 bx0@@10) t1@@14)))
 :qid |DafnyPre.515:12|
 :skolemid |664|
 :pattern ( (Apply1 t0@@23 t1@@14 h@@23 f@@13 bx0@@10))
))) (=> (forall ((h@@24 T@U) (bx0@@11 T@U) ) (!  (=> (and (= (type h@@24) (MapType0Type refType MapType1Type)) (= (type bx0@@11) BoxType)) (=> (and (and ($IsGoodHeap h@@24) ($IsBox bx0@@11 t0@@23)) (Requires1 t0@@23 t1@@14 h@@24 f@@13 bx0@@11)) ($IsBox (Apply1 t0@@23 t1@@14 h@@24 f@@13 bx0@@11) t1@@14)))
 :qid |DafnyPre.515:12|
 :skolemid |664|
 :pattern ( (Apply1 t0@@23 t1@@14 h@@24 f@@13 bx0@@11))
)) ($Is f@@13 (Tclass._System.___hFunc1 t0@@23 t1@@14)))))
 :qid |unknown.0:0|
 :skolemid |665|
 :pattern ( ($Is f@@13 (Tclass._System.___hFunc1 t0@@23 t1@@14)))
)))
(assert (forall ((f@@14 T@U) (t0@@24 T@U) (t1@@15 T@U) (u0 T@U) (u1 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@14) HandleTypeType) (= (type t0@@24) TyType)) (= (type t1@@15) TyType)) (= (type u0) TyType)) (= (type u1) TyType)) (and (and ($Is f@@14 (Tclass._System.___hFunc1 t0@@24 t1@@15)) (forall ((bx@@41 T@U) ) (!  (=> (and (= (type bx@@41) BoxType) ($IsBox bx@@41 u0)) ($IsBox bx@@41 t0@@24))
 :qid |unknown.0:0|
 :skolemid |666|
 :pattern ( ($IsBox bx@@41 u0))
 :pattern ( ($IsBox bx@@41 t0@@24))
))) (forall ((bx@@42 T@U) ) (!  (=> (and (= (type bx@@42) BoxType) ($IsBox bx@@42 t1@@15)) ($IsBox bx@@42 u1))
 :qid |unknown.0:0|
 :skolemid |667|
 :pattern ( ($IsBox bx@@42 t1@@15))
 :pattern ( ($IsBox bx@@42 u1))
)))) ($Is f@@14 (Tclass._System.___hFunc1 u0 u1)))
 :qid |unknown.0:0|
 :skolemid |668|
 :pattern ( ($Is f@@14 (Tclass._System.___hFunc1 t0@@24 t1@@15)) ($Is f@@14 (Tclass._System.___hFunc1 u0 u1)))
)))
(assert (forall ((f@@15 T@U) (t0@@25 T@U) (t1@@16 T@U) (h@@25 T@U) ) (!  (=> (and (and (and (and (= (type f@@15) HandleTypeType) (= (type t0@@25) TyType)) (= (type t1@@16) TyType)) (= (type h@@25) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@25)) (and (=> ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@25 t1@@16) h@@25) (forall ((bx0@@12 T@U) ) (!  (=> (= (type bx0@@12) BoxType) (=> (and (and ($IsBox bx0@@12 t0@@25) ($IsAllocBox bx0@@12 t0@@25 h@@25)) (Requires1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12)) (forall ((r@@9 T@U) ) (!  (=> (= (type r@@9) refType) (=> (and (not (= r@@9 null)) (U_2_bool (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12) ($Box r@@9)))) (U_2_bool (MapType1Select (MapType0Select h@@25 r@@9) alloc))))
 :qid |unknown.0:0|
 :skolemid |669|
 :pattern ( (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12) ($Box r@@9)))
))))
 :qid |unknown.0:0|
 :skolemid |670|
 :pattern ( (Apply1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12))
 :pattern ( (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@12))
))) (=> (forall ((bx0@@13 T@U) ) (!  (=> (= (type bx0@@13) BoxType) (=> (and (and ($IsBox bx0@@13 t0@@25) ($IsAllocBox bx0@@13 t0@@25 h@@25)) (Requires1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13)) (forall ((r@@10 T@U) ) (!  (=> (= (type r@@10) refType) (=> (and (not (= r@@10 null)) (U_2_bool (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13) ($Box r@@10)))) (U_2_bool (MapType1Select (MapType0Select h@@25 r@@10) alloc))))
 :qid |unknown.0:0|
 :skolemid |669|
 :pattern ( (MapType0Select (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13) ($Box r@@10)))
))))
 :qid |unknown.0:0|
 :skolemid |670|
 :pattern ( (Apply1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13))
 :pattern ( (Reads1 t0@@25 t1@@16 h@@25 f@@15 bx0@@13))
)) ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@25 t1@@16) h@@25))))
 :qid |unknown.0:0|
 :skolemid |671|
 :pattern ( ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@25 t1@@16) h@@25))
)))
(assert (forall ((f@@16 T@U) (t0@@26 T@U) (t1@@17 T@U) (h@@26 T@U) ) (!  (=> (and (and (and (and (= (type f@@16) HandleTypeType) (= (type t0@@26) TyType)) (= (type t1@@17) TyType)) (= (type h@@26) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@26) ($IsAlloc f@@16 (Tclass._System.___hFunc1 t0@@26 t1@@17) h@@26))) (forall ((bx0@@14 T@U) ) (!  (=> (= (type bx0@@14) BoxType) (=> (and ($IsAllocBox bx0@@14 t0@@26 h@@26) (Requires1 t0@@26 t1@@17 h@@26 f@@16 bx0@@14)) ($IsAllocBox (Apply1 t0@@26 t1@@17 h@@26 f@@16 bx0@@14) t1@@17 h@@26)))
 :qid |unknown.0:0|
 :skolemid |672|
 :pattern ( (Apply1 t0@@26 t1@@17 h@@26 f@@16 bx0@@14))
)))
 :qid |unknown.0:0|
 :skolemid |673|
 :pattern ( ($IsAlloc f@@16 (Tclass._System.___hFunc1 t0@@26 t1@@17) h@@26))
)))
(assert (forall ((arg0@@123 T@U) (arg1@@56 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1 arg0@@123 arg1@@56)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1|
 :pattern ( (Tclass._System.___hPartialFunc1 arg0@@123 arg1@@56))
)))
(assert (forall ((|#$T0@@3| T@U) (|#$R@@3| T@U) ) (!  (=> (and (= (type |#$T0@@3|) TyType) (= (type |#$R@@3|) TyType)) (= (Tag (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@3|)) Tagclass._System.___hPartialFunc1))
 :qid |unknown.0:0|
 :skolemid |674|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@3|))
)))
(assert (forall ((arg0@@124 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_0 arg0@@124)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_0|
 :pattern ( (Tclass._System.___hPartialFunc1_0 arg0@@124))
)))
(assert (forall ((|#$T0@@4| T@U) (|#$R@@4| T@U) ) (!  (=> (and (= (type |#$T0@@4|) TyType) (= (type |#$R@@4|) TyType)) (= (Tclass._System.___hPartialFunc1_0 (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@4|)) |#$T0@@4|))
 :qid |unknown.0:0|
 :skolemid |675|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@4|))
)))
(assert (forall ((arg0@@125 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_1 arg0@@125)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_1|
 :pattern ( (Tclass._System.___hPartialFunc1_1 arg0@@125))
)))
(assert (forall ((|#$T0@@5| T@U) (|#$R@@5| T@U) ) (!  (=> (and (= (type |#$T0@@5|) TyType) (= (type |#$R@@5|) TyType)) (= (Tclass._System.___hPartialFunc1_1 (Tclass._System.___hPartialFunc1 |#$T0@@5| |#$R@@5|)) |#$R@@5|))
 :qid |unknown.0:0|
 :skolemid |676|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@5| |#$R@@5|))
)))
(assert (forall ((|#$T0@@6| T@U) (|#$R@@6| T@U) (bx@@43 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@6|) TyType) (= (type |#$R@@6|) TyType)) (= (type bx@@43) BoxType)) ($IsBox bx@@43 (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|))) (and (= ($Box ($Unbox HandleTypeType bx@@43)) bx@@43) ($Is ($Unbox HandleTypeType bx@@43) (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|))))
 :qid |unknown.0:0|
 :skolemid |677|
 :pattern ( ($IsBox bx@@43 (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|)))
)))
(assert (forall ((|#$T0@@7| T@U) (|#$R@@7| T@U) (|f#0| T@U) ) (!  (=> (and (and (= (type |#$T0@@7|) TyType) (= (type |#$R@@7|) TyType)) (= (type |f#0|) HandleTypeType)) (and (=> ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|)) (and ($Is |f#0| (Tclass._System.___hFunc1 |#$T0@@7| |#$R@@7|)) (forall ((|x0#0| T@U) ) (!  (=> (and (= (type |x0#0|) BoxType) ($IsBox |x0#0| |#$T0@@7|)) (|Set#Equal| (Reads1 |#$T0@@7| |#$R@@7| $OneHeap |f#0| |x0#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |678|
 :no-pattern (type |x0#0|)
 :no-pattern (U_2_int |x0#0|)
 :no-pattern (U_2_bool |x0#0|)
)))) (=> (and ($Is |f#0| (Tclass._System.___hFunc1 |#$T0@@7| |#$R@@7|)) (forall ((|x0#0@@0| T@U) ) (!  (=> (and (= (type |x0#0@@0|) BoxType) ($IsBox |x0#0@@0| |#$T0@@7|)) (|Set#Equal| (Reads1 |#$T0@@7| |#$R@@7| $OneHeap |f#0| |x0#0@@0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |678|
 :no-pattern (type |x0#0@@0|)
 :no-pattern (U_2_int |x0#0@@0|)
 :no-pattern (U_2_bool |x0#0@@0|)
))) ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|)))))
 :qid |unknown.0:0|
 :skolemid |679|
 :pattern ( ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|)))
)))
(assert (forall ((|#$T0@@8| T@U) (|#$R@@8| T@U) (|f#0@@0| T@U) ($h@@7 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@8|) TyType) (= (type |#$R@@8|) TyType)) (= (type |f#0@@0|) HandleTypeType)) (= (type $h@@7) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7) ($IsAlloc |f#0@@0| (Tclass._System.___hFunc1 |#$T0@@8| |#$R@@8|) $h@@7)) (=> ($IsAlloc |f#0@@0| (Tclass._System.___hFunc1 |#$T0@@8| |#$R@@8|) $h@@7) ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7))))
 :qid |unknown.0:0|
 :skolemid |680|
 :pattern ( ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7))
)))
(assert (forall ((arg0@@126 T@U) (arg1@@57 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1 arg0@@126 arg1@@57)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1|
 :pattern ( (Tclass._System.___hTotalFunc1 arg0@@126 arg1@@57))
)))
(assert (forall ((|#$T0@@9| T@U) (|#$R@@9| T@U) ) (!  (=> (and (= (type |#$T0@@9|) TyType) (= (type |#$R@@9|) TyType)) (= (Tag (Tclass._System.___hTotalFunc1 |#$T0@@9| |#$R@@9|)) Tagclass._System.___hTotalFunc1))
 :qid |unknown.0:0|
 :skolemid |681|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@9| |#$R@@9|))
)))
(assert (forall ((arg0@@127 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_0 arg0@@127)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_0|
 :pattern ( (Tclass._System.___hTotalFunc1_0 arg0@@127))
)))
(assert (forall ((|#$T0@@10| T@U) (|#$R@@10| T@U) ) (!  (=> (and (= (type |#$T0@@10|) TyType) (= (type |#$R@@10|) TyType)) (= (Tclass._System.___hTotalFunc1_0 (Tclass._System.___hTotalFunc1 |#$T0@@10| |#$R@@10|)) |#$T0@@10|))
 :qid |unknown.0:0|
 :skolemid |682|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@10| |#$R@@10|))
)))
(assert (forall ((arg0@@128 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_1 arg0@@128)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_1|
 :pattern ( (Tclass._System.___hTotalFunc1_1 arg0@@128))
)))
(assert (forall ((|#$T0@@11| T@U) (|#$R@@11| T@U) ) (!  (=> (and (= (type |#$T0@@11|) TyType) (= (type |#$R@@11|) TyType)) (= (Tclass._System.___hTotalFunc1_1 (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@11|)) |#$R@@11|))
 :qid |unknown.0:0|
 :skolemid |683|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@11|))
)))
(assert (forall ((|#$T0@@12| T@U) (|#$R@@12| T@U) (bx@@44 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@12|) TyType) (= (type |#$R@@12|) TyType)) (= (type bx@@44) BoxType)) ($IsBox bx@@44 (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|))) (and (= ($Box ($Unbox HandleTypeType bx@@44)) bx@@44) ($Is ($Unbox HandleTypeType bx@@44) (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|))))
 :qid |unknown.0:0|
 :skolemid |684|
 :pattern ( ($IsBox bx@@44 (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|)))
)))
(assert (forall ((|#$T0@@13| T@U) (|#$R@@13| T@U) (|f#0@@1| T@U) ) (!  (=> (and (and (= (type |#$T0@@13|) TyType) (= (type |#$R@@13|) TyType)) (= (type |f#0@@1|) HandleTypeType)) (and (=> ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|)) (and ($Is |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@13|)) (forall ((|x0#0@@1| T@U) ) (!  (=> (and (= (type |x0#0@@1|) BoxType) ($IsBox |x0#0@@1| |#$T0@@13|)) (Requires1 |#$T0@@13| |#$R@@13| $OneHeap |f#0@@1| |x0#0@@1|))
 :qid |unknown.0:0|
 :skolemid |685|
 :no-pattern (type |x0#0@@1|)
 :no-pattern (U_2_int |x0#0@@1|)
 :no-pattern (U_2_bool |x0#0@@1|)
)))) (=> (and ($Is |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@13|)) (forall ((|x0#0@@2| T@U) ) (!  (=> (and (= (type |x0#0@@2|) BoxType) ($IsBox |x0#0@@2| |#$T0@@13|)) (Requires1 |#$T0@@13| |#$R@@13| $OneHeap |f#0@@1| |x0#0@@2|))
 :qid |unknown.0:0|
 :skolemid |685|
 :no-pattern (type |x0#0@@2|)
 :no-pattern (U_2_int |x0#0@@2|)
 :no-pattern (U_2_bool |x0#0@@2|)
))) ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|)))))
 :qid |unknown.0:0|
 :skolemid |686|
 :pattern ( ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|)))
)))
(assert (forall ((|#$T0@@14| T@U) (|#$R@@14| T@U) (|f#0@@2| T@U) ($h@@8 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@14|) TyType) (= (type |#$R@@14|) TyType)) (= (type |f#0@@2|) HandleTypeType)) (= (type $h@@8) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8) ($IsAlloc |f#0@@2| (Tclass._System.___hPartialFunc1 |#$T0@@14| |#$R@@14|) $h@@8)) (=> ($IsAlloc |f#0@@2| (Tclass._System.___hPartialFunc1 |#$T0@@14| |#$R@@14|) $h@@8) ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8))))
 :qid |unknown.0:0|
 :skolemid |687|
 :pattern ( ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8))
)))
(assert (forall ((arg0@@129 T@U) ) (! (= (type (Tclass._System.___hFunc0 arg0@@129)) TyType)
 :qid |funType:Tclass._System.___hFunc0|
 :pattern ( (Tclass._System.___hFunc0 arg0@@129))
)))
(assert (forall ((|#$R@@15| T@U) ) (!  (=> (= (type |#$R@@15|) TyType) (= (Tag (Tclass._System.___hFunc0 |#$R@@15|)) Tagclass._System.___hFunc0))
 :qid |unknown.0:0|
 :skolemid |688|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@15|))
)))
(assert (forall ((arg0@@130 T@U) ) (! (= (type (Tclass._System.___hFunc0_0 arg0@@130)) TyType)
 :qid |funType:Tclass._System.___hFunc0_0|
 :pattern ( (Tclass._System.___hFunc0_0 arg0@@130))
)))
(assert (forall ((|#$R@@16| T@U) ) (!  (=> (= (type |#$R@@16|) TyType) (= (Tclass._System.___hFunc0_0 (Tclass._System.___hFunc0 |#$R@@16|)) |#$R@@16|))
 :qid |unknown.0:0|
 :skolemid |689|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@16|))
)))
(assert (forall ((|#$R@@17| T@U) (bx@@45 T@U) ) (!  (=> (and (and (= (type |#$R@@17|) TyType) (= (type bx@@45) BoxType)) ($IsBox bx@@45 (Tclass._System.___hFunc0 |#$R@@17|))) (and (= ($Box ($Unbox HandleTypeType bx@@45)) bx@@45) ($Is ($Unbox HandleTypeType bx@@45) (Tclass._System.___hFunc0 |#$R@@17|))))
 :qid |unknown.0:0|
 :skolemid |690|
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
 :skolemid |691|
 :pattern ( (Apply0 t0@@27 heap@@6 (Handle0 h@@27 r@@11 rd@@2)))
)))
(assert (forall ((t0@@28 T@U) (heap@@7 T@U) (h@@28 T@U) (r@@12 T@U) (rd@@3 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@28) TyType) (= (type heap@@7) (MapType0Type refType MapType1Type))) (= (type h@@28) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@12) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@3) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (U_2_bool (MapType0Select r@@12 heap@@7))) (Requires0 t0@@28 heap@@7 (Handle0 h@@28 r@@12 rd@@3)))
 :qid |unknown.0:0|
 :skolemid |692|
 :pattern ( (Requires0 t0@@28 heap@@7 (Handle0 h@@28 r@@12 rd@@3)))
)))
(assert (forall ((arg0@@133 T@U) (arg1@@60 T@U) (arg2@@18 T@U) ) (! (= (type (Reads0 arg0@@133 arg1@@60 arg2@@18)) (MapType0Type BoxType boolType))
 :qid |funType:Reads0|
 :pattern ( (Reads0 arg0@@133 arg1@@60 arg2@@18))
)))
(assert (forall ((t0@@29 T@U) (heap@@8 T@U) (h@@29 T@U) (r@@13 T@U) (rd@@4 T@U) (bx@@46 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@29) TyType) (= (type heap@@8) (MapType0Type refType MapType1Type))) (= (type h@@29) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@13) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@4) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (= (type bx@@46) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads0 t0@@29 heap@@8 (Handle0 h@@29 r@@13 rd@@4)) bx@@46)) (U_2_bool (MapType0Select (MapType0Select rd@@4 heap@@8) bx@@46))) (=> (U_2_bool (MapType0Select (MapType0Select rd@@4 heap@@8) bx@@46)) (U_2_bool (MapType0Select (Reads0 t0@@29 heap@@8 (Handle0 h@@29 r@@13 rd@@4)) bx@@46)))))
 :qid |unknown.0:0|
 :skolemid |693|
 :pattern ( (MapType0Select (Reads0 t0@@29 heap@@8 (Handle0 h@@29 r@@13 rd@@4)) bx@@46))
)))
(assert (forall ((t0@@30 T@U) (h0@@6 T@U) (h1@@6 T@U) (f@@17 T@U) ) (!  (=> (and (and (and (and (= (type t0@@30) TyType) (= (type h0@@6) (MapType0Type refType MapType1Type))) (= (type h1@@6) (MapType0Type refType MapType1Type))) (= (type f@@17) HandleTypeType)) (and (and (and ($HeapSucc h0@@6 h1@@6) (and ($IsGoodHeap h0@@6) ($IsGoodHeap h1@@6))) ($Is f@@17 (Tclass._System.___hFunc0 t0@@30))) (forall ((o@@60 T@U) (fld@@5 T@U) ) (! (let ((a@@85 (FieldTypeInv0 (type fld@@5))))
 (=> (and (and (= (type o@@60) refType) (= (type fld@@5) (FieldType a@@85))) (and (not (= o@@60 null)) (U_2_bool (MapType0Select (Reads0 t0@@30 h0@@6 f@@17) ($Box o@@60))))) (= (MapType1Select (MapType0Select h0@@6 o@@60) fld@@5) (MapType1Select (MapType0Select h1@@6 o@@60) fld@@5))))
 :qid |unknown.0:0|
 :skolemid |694|
 :no-pattern (type o@@60)
 :no-pattern (type fld@@5)
 :no-pattern (U_2_int o@@60)
 :no-pattern (U_2_bool o@@60)
 :no-pattern (U_2_int fld@@5)
 :no-pattern (U_2_bool fld@@5)
)))) (= (Reads0 t0@@30 h0@@6 f@@17) (Reads0 t0@@30 h1@@6 f@@17)))
 :qid |unknown.0:0|
 :skolemid |695|
 :pattern ( ($HeapSucc h0@@6 h1@@6) (Reads0 t0@@30 h1@@6 f@@17))
)))
(assert (forall ((t0@@31 T@U) (h0@@7 T@U) (h1@@7 T@U) (f@@18 T@U) ) (!  (=> (and (and (and (and (= (type t0@@31) TyType) (= (type h0@@7) (MapType0Type refType MapType1Type))) (= (type h1@@7) (MapType0Type refType MapType1Type))) (= (type f@@18) HandleTypeType)) (and (and (and ($HeapSucc h0@@7 h1@@7) (and ($IsGoodHeap h0@@7) ($IsGoodHeap h1@@7))) ($Is f@@18 (Tclass._System.___hFunc0 t0@@31))) (forall ((o@@61 T@U) (fld@@6 T@U) ) (! (let ((a@@86 (FieldTypeInv0 (type fld@@6))))
 (=> (and (and (= (type o@@61) refType) (= (type fld@@6) (FieldType a@@86))) (and (not (= o@@61 null)) (U_2_bool (MapType0Select (Reads0 t0@@31 h1@@7 f@@18) ($Box o@@61))))) (= (MapType1Select (MapType0Select h0@@7 o@@61) fld@@6) (MapType1Select (MapType0Select h1@@7 o@@61) fld@@6))))
 :qid |unknown.0:0|
 :skolemid |696|
 :no-pattern (type o@@61)
 :no-pattern (type fld@@6)
 :no-pattern (U_2_int o@@61)
 :no-pattern (U_2_bool o@@61)
 :no-pattern (U_2_int fld@@6)
 :no-pattern (U_2_bool fld@@6)
)))) (= (Reads0 t0@@31 h0@@7 f@@18) (Reads0 t0@@31 h1@@7 f@@18)))
 :qid |unknown.0:0|
 :skolemid |697|
 :pattern ( ($HeapSucc h0@@7 h1@@7) (Reads0 t0@@31 h1@@7 f@@18))
)))
(assert (forall ((t0@@32 T@U) (h0@@8 T@U) (h1@@8 T@U) (f@@19 T@U) ) (!  (=> (and (and (and (and (= (type t0@@32) TyType) (= (type h0@@8) (MapType0Type refType MapType1Type))) (= (type h1@@8) (MapType0Type refType MapType1Type))) (= (type f@@19) HandleTypeType)) (and (and (and ($HeapSucc h0@@8 h1@@8) (and ($IsGoodHeap h0@@8) ($IsGoodHeap h1@@8))) ($Is f@@19 (Tclass._System.___hFunc0 t0@@32))) (forall ((o@@62 T@U) (fld@@7 T@U) ) (! (let ((a@@87 (FieldTypeInv0 (type fld@@7))))
 (=> (and (and (= (type o@@62) refType) (= (type fld@@7) (FieldType a@@87))) (and (not (= o@@62 null)) (U_2_bool (MapType0Select (Reads0 t0@@32 h0@@8 f@@19) ($Box o@@62))))) (= (MapType1Select (MapType0Select h0@@8 o@@62) fld@@7) (MapType1Select (MapType0Select h1@@8 o@@62) fld@@7))))
 :qid |unknown.0:0|
 :skolemid |698|
 :no-pattern (type o@@62)
 :no-pattern (type fld@@7)
 :no-pattern (U_2_int o@@62)
 :no-pattern (U_2_bool o@@62)
 :no-pattern (U_2_int fld@@7)
 :no-pattern (U_2_bool fld@@7)
)))) (and (=> (Requires0 t0@@32 h0@@8 f@@19) (Requires0 t0@@32 h1@@8 f@@19)) (=> (Requires0 t0@@32 h1@@8 f@@19) (Requires0 t0@@32 h0@@8 f@@19))))
 :qid |unknown.0:0|
 :skolemid |699|
 :pattern ( ($HeapSucc h0@@8 h1@@8) (Requires0 t0@@32 h1@@8 f@@19))
)))
(assert (forall ((t0@@33 T@U) (h0@@9 T@U) (h1@@9 T@U) (f@@20 T@U) ) (!  (=> (and (and (and (and (= (type t0@@33) TyType) (= (type h0@@9) (MapType0Type refType MapType1Type))) (= (type h1@@9) (MapType0Type refType MapType1Type))) (= (type f@@20) HandleTypeType)) (and (and (and ($HeapSucc h0@@9 h1@@9) (and ($IsGoodHeap h0@@9) ($IsGoodHeap h1@@9))) ($Is f@@20 (Tclass._System.___hFunc0 t0@@33))) (forall ((o@@63 T@U) (fld@@8 T@U) ) (! (let ((a@@88 (FieldTypeInv0 (type fld@@8))))
 (=> (and (and (= (type o@@63) refType) (= (type fld@@8) (FieldType a@@88))) (and (not (= o@@63 null)) (U_2_bool (MapType0Select (Reads0 t0@@33 h1@@9 f@@20) ($Box o@@63))))) (= (MapType1Select (MapType0Select h0@@9 o@@63) fld@@8) (MapType1Select (MapType0Select h1@@9 o@@63) fld@@8))))
 :qid |unknown.0:0|
 :skolemid |700|
 :no-pattern (type o@@63)
 :no-pattern (type fld@@8)
 :no-pattern (U_2_int o@@63)
 :no-pattern (U_2_bool o@@63)
 :no-pattern (U_2_int fld@@8)
 :no-pattern (U_2_bool fld@@8)
)))) (and (=> (Requires0 t0@@33 h0@@9 f@@20) (Requires0 t0@@33 h1@@9 f@@20)) (=> (Requires0 t0@@33 h1@@9 f@@20) (Requires0 t0@@33 h0@@9 f@@20))))
 :qid |unknown.0:0|
 :skolemid |701|
 :pattern ( ($HeapSucc h0@@9 h1@@9) (Requires0 t0@@33 h1@@9 f@@20))
)))
(assert (forall ((t0@@34 T@U) (h0@@10 T@U) (h1@@10 T@U) (f@@21 T@U) ) (!  (=> (and (and (and (and (= (type t0@@34) TyType) (= (type h0@@10) (MapType0Type refType MapType1Type))) (= (type h1@@10) (MapType0Type refType MapType1Type))) (= (type f@@21) HandleTypeType)) (and (and (and ($HeapSucc h0@@10 h1@@10) (and ($IsGoodHeap h0@@10) ($IsGoodHeap h1@@10))) ($Is f@@21 (Tclass._System.___hFunc0 t0@@34))) (forall ((o@@64 T@U) (fld@@9 T@U) ) (! (let ((a@@89 (FieldTypeInv0 (type fld@@9))))
 (=> (and (and (= (type o@@64) refType) (= (type fld@@9) (FieldType a@@89))) (and (not (= o@@64 null)) (U_2_bool (MapType0Select (Reads0 t0@@34 h0@@10 f@@21) ($Box o@@64))))) (= (MapType1Select (MapType0Select h0@@10 o@@64) fld@@9) (MapType1Select (MapType0Select h1@@10 o@@64) fld@@9))))
 :qid |unknown.0:0|
 :skolemid |702|
 :no-pattern (type o@@64)
 :no-pattern (type fld@@9)
 :no-pattern (U_2_int o@@64)
 :no-pattern (U_2_bool o@@64)
 :no-pattern (U_2_int fld@@9)
 :no-pattern (U_2_bool fld@@9)
)))) (= (Apply0 t0@@34 h0@@10 f@@21) (Apply0 t0@@34 h1@@10 f@@21)))
 :qid |unknown.0:0|
 :skolemid |703|
 :pattern ( ($HeapSucc h0@@10 h1@@10) (Apply0 t0@@34 h1@@10 f@@21))
)))
(assert (forall ((t0@@35 T@U) (h0@@11 T@U) (h1@@11 T@U) (f@@22 T@U) ) (!  (=> (and (and (and (and (= (type t0@@35) TyType) (= (type h0@@11) (MapType0Type refType MapType1Type))) (= (type h1@@11) (MapType0Type refType MapType1Type))) (= (type f@@22) HandleTypeType)) (and (and (and ($HeapSucc h0@@11 h1@@11) (and ($IsGoodHeap h0@@11) ($IsGoodHeap h1@@11))) ($Is f@@22 (Tclass._System.___hFunc0 t0@@35))) (forall ((o@@65 T@U) (fld@@10 T@U) ) (! (let ((a@@90 (FieldTypeInv0 (type fld@@10))))
 (=> (and (and (= (type o@@65) refType) (= (type fld@@10) (FieldType a@@90))) (and (not (= o@@65 null)) (U_2_bool (MapType0Select (Reads0 t0@@35 h1@@11 f@@22) ($Box o@@65))))) (= (MapType1Select (MapType0Select h0@@11 o@@65) fld@@10) (MapType1Select (MapType0Select h1@@11 o@@65) fld@@10))))
 :qid |unknown.0:0|
 :skolemid |704|
 :no-pattern (type o@@65)
 :no-pattern (type fld@@10)
 :no-pattern (U_2_int o@@65)
 :no-pattern (U_2_bool o@@65)
 :no-pattern (U_2_int fld@@10)
 :no-pattern (U_2_bool fld@@10)
)))) (= (Apply0 t0@@35 h0@@11 f@@22) (Apply0 t0@@35 h1@@11 f@@22)))
 :qid |unknown.0:0|
 :skolemid |705|
 :pattern ( ($HeapSucc h0@@11 h1@@11) (Apply0 t0@@35 h1@@11 f@@22))
)))
(assert (forall ((t0@@36 T@U) (heap@@9 T@U) (f@@23 T@U) ) (!  (=> (and (and (and (= (type t0@@36) TyType) (= (type heap@@9) (MapType0Type refType MapType1Type))) (= (type f@@23) HandleTypeType)) (and ($IsGoodHeap heap@@9) ($Is f@@23 (Tclass._System.___hFunc0 t0@@36)))) (and (=> (|Set#Equal| (Reads0 t0@@36 $OneHeap f@@23) (|Set#Empty| BoxType)) (|Set#Equal| (Reads0 t0@@36 heap@@9 f@@23) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads0 t0@@36 heap@@9 f@@23) (|Set#Empty| BoxType)) (|Set#Equal| (Reads0 t0@@36 $OneHeap f@@23) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |706|
 :pattern ( (Reads0 t0@@36 $OneHeap f@@23) ($IsGoodHeap heap@@9))
 :pattern ( (Reads0 t0@@36 heap@@9 f@@23))
)))
(assert (forall ((t0@@37 T@U) (heap@@10 T@U) (f@@24 T@U) ) (!  (=> (and (and (and (= (type t0@@37) TyType) (= (type heap@@10) (MapType0Type refType MapType1Type))) (= (type f@@24) HandleTypeType)) (and (and ($IsGoodHeap heap@@10) ($Is f@@24 (Tclass._System.___hFunc0 t0@@37))) (|Set#Equal| (Reads0 t0@@37 $OneHeap f@@24) (|Set#Empty| BoxType)))) (and (=> (Requires0 t0@@37 $OneHeap f@@24) (Requires0 t0@@37 heap@@10 f@@24)) (=> (Requires0 t0@@37 heap@@10 f@@24) (Requires0 t0@@37 $OneHeap f@@24))))
 :qid |unknown.0:0|
 :skolemid |707|
 :pattern ( (Requires0 t0@@37 $OneHeap f@@24) ($IsGoodHeap heap@@10))
 :pattern ( (Requires0 t0@@37 heap@@10 f@@24))
)))
(assert (forall ((f@@25 T@U) (t0@@38 T@U) ) (!  (=> (and (= (type f@@25) HandleTypeType) (= (type t0@@38) TyType)) (and (=> ($Is f@@25 (Tclass._System.___hFunc0 t0@@38)) (forall ((h@@30 T@U) ) (!  (=> (= (type h@@30) (MapType0Type refType MapType1Type)) (=> (and ($IsGoodHeap h@@30) (Requires0 t0@@38 h@@30 f@@25)) ($IsBox (Apply0 t0@@38 h@@30 f@@25) t0@@38)))
 :qid |DafnyPre.515:12|
 :skolemid |708|
 :pattern ( (Apply0 t0@@38 h@@30 f@@25))
))) (=> (forall ((h@@31 T@U) ) (!  (=> (= (type h@@31) (MapType0Type refType MapType1Type)) (=> (and ($IsGoodHeap h@@31) (Requires0 t0@@38 h@@31 f@@25)) ($IsBox (Apply0 t0@@38 h@@31 f@@25) t0@@38)))
 :qid |DafnyPre.515:12|
 :skolemid |708|
 :pattern ( (Apply0 t0@@38 h@@31 f@@25))
)) ($Is f@@25 (Tclass._System.___hFunc0 t0@@38)))))
 :qid |unknown.0:0|
 :skolemid |709|
 :pattern ( ($Is f@@25 (Tclass._System.___hFunc0 t0@@38)))
)))
(assert (forall ((f@@26 T@U) (t0@@39 T@U) (u0@@0 T@U) ) (!  (=> (and (and (and (= (type f@@26) HandleTypeType) (= (type t0@@39) TyType)) (= (type u0@@0) TyType)) (and ($Is f@@26 (Tclass._System.___hFunc0 t0@@39)) (forall ((bx@@47 T@U) ) (!  (=> (and (= (type bx@@47) BoxType) ($IsBox bx@@47 t0@@39)) ($IsBox bx@@47 u0@@0))
 :qid |unknown.0:0|
 :skolemid |710|
 :pattern ( ($IsBox bx@@47 t0@@39))
 :pattern ( ($IsBox bx@@47 u0@@0))
)))) ($Is f@@26 (Tclass._System.___hFunc0 u0@@0)))
 :qid |unknown.0:0|
 :skolemid |711|
 :pattern ( ($Is f@@26 (Tclass._System.___hFunc0 t0@@39)) ($Is f@@26 (Tclass._System.___hFunc0 u0@@0)))
)))
(assert (forall ((f@@27 T@U) (t0@@40 T@U) (h@@32 T@U) ) (!  (=> (and (and (and (= (type f@@27) HandleTypeType) (= (type t0@@40) TyType)) (= (type h@@32) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@32)) (and (=> ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@40) h@@32) (=> (Requires0 t0@@40 h@@32 f@@27) (forall ((r@@14 T@U) ) (!  (=> (= (type r@@14) refType) (=> (and (not (= r@@14 null)) (U_2_bool (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@14)))) (U_2_bool (MapType1Select (MapType0Select h@@32 r@@14) alloc))))
 :qid |unknown.0:0|
 :skolemid |712|
 :pattern ( (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@14)))
)))) (=> (=> (Requires0 t0@@40 h@@32 f@@27) (forall ((r@@15 T@U) ) (!  (=> (= (type r@@15) refType) (=> (and (not (= r@@15 null)) (U_2_bool (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@15)))) (U_2_bool (MapType1Select (MapType0Select h@@32 r@@15) alloc))))
 :qid |unknown.0:0|
 :skolemid |712|
 :pattern ( (MapType0Select (Reads0 t0@@40 h@@32 f@@27) ($Box r@@15)))
))) ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@40) h@@32))))
 :qid |unknown.0:0|
 :skolemid |713|
 :pattern ( ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@40) h@@32))
)))
(assert (forall ((f@@28 T@U) (t0@@41 T@U) (h@@33 T@U) ) (!  (=> (and (and (and (and (= (type f@@28) HandleTypeType) (= (type t0@@41) TyType)) (= (type h@@33) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@33) ($IsAlloc f@@28 (Tclass._System.___hFunc0 t0@@41) h@@33))) (Requires0 t0@@41 h@@33 f@@28)) ($IsAllocBox (Apply0 t0@@41 h@@33 f@@28) t0@@41 h@@33))
 :qid |unknown.0:0|
 :skolemid |714|
 :pattern ( ($IsAlloc f@@28 (Tclass._System.___hFunc0 t0@@41) h@@33))
)))
(assert (forall ((arg0@@134 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0 arg0@@134)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0|
 :pattern ( (Tclass._System.___hPartialFunc0 arg0@@134))
)))
(assert (forall ((|#$R@@18| T@U) ) (!  (=> (= (type |#$R@@18|) TyType) (= (Tag (Tclass._System.___hPartialFunc0 |#$R@@18|)) Tagclass._System.___hPartialFunc0))
 :qid |unknown.0:0|
 :skolemid |715|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@18|))
)))
(assert (forall ((arg0@@135 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0_0 arg0@@135)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0_0|
 :pattern ( (Tclass._System.___hPartialFunc0_0 arg0@@135))
)))
(assert (forall ((|#$R@@19| T@U) ) (!  (=> (= (type |#$R@@19|) TyType) (= (Tclass._System.___hPartialFunc0_0 (Tclass._System.___hPartialFunc0 |#$R@@19|)) |#$R@@19|))
 :qid |unknown.0:0|
 :skolemid |716|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@19|))
)))
(assert (forall ((|#$R@@20| T@U) (bx@@48 T@U) ) (!  (=> (and (and (= (type |#$R@@20|) TyType) (= (type bx@@48) BoxType)) ($IsBox bx@@48 (Tclass._System.___hPartialFunc0 |#$R@@20|))) (and (= ($Box ($Unbox HandleTypeType bx@@48)) bx@@48) ($Is ($Unbox HandleTypeType bx@@48) (Tclass._System.___hPartialFunc0 |#$R@@20|))))
 :qid |unknown.0:0|
 :skolemid |717|
 :pattern ( ($IsBox bx@@48 (Tclass._System.___hPartialFunc0 |#$R@@20|)))
)))
(assert (forall ((|#$R@@21| T@U) (|f#0@@3| T@U) ) (!  (=> (and (= (type |#$R@@21|) TyType) (= (type |f#0@@3|) HandleTypeType)) (and (=> ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|)) (and ($Is |f#0@@3| (Tclass._System.___hFunc0 |#$R@@21|)) (|Set#Equal| (Reads0 |#$R@@21| $OneHeap |f#0@@3|) (|Set#Empty| BoxType)))) (=> (and ($Is |f#0@@3| (Tclass._System.___hFunc0 |#$R@@21|)) (|Set#Equal| (Reads0 |#$R@@21| $OneHeap |f#0@@3|) (|Set#Empty| BoxType))) ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|)))))
 :qid |unknown.0:0|
 :skolemid |718|
 :pattern ( ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|)))
)))
(assert (forall ((|#$R@@22| T@U) (|f#0@@4| T@U) ($h@@9 T@U) ) (!  (=> (and (and (= (type |#$R@@22|) TyType) (= (type |f#0@@4|) HandleTypeType)) (= (type $h@@9) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9) ($IsAlloc |f#0@@4| (Tclass._System.___hFunc0 |#$R@@22|) $h@@9)) (=> ($IsAlloc |f#0@@4| (Tclass._System.___hFunc0 |#$R@@22|) $h@@9) ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9))))
 :qid |unknown.0:0|
 :skolemid |719|
 :pattern ( ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9))
)))
(assert (forall ((arg0@@136 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0 arg0@@136)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0|
 :pattern ( (Tclass._System.___hTotalFunc0 arg0@@136))
)))
(assert (forall ((|#$R@@23| T@U) ) (!  (=> (= (type |#$R@@23|) TyType) (= (Tag (Tclass._System.___hTotalFunc0 |#$R@@23|)) Tagclass._System.___hTotalFunc0))
 :qid |unknown.0:0|
 :skolemid |720|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@23|))
)))
(assert (forall ((arg0@@137 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0_0 arg0@@137)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0_0|
 :pattern ( (Tclass._System.___hTotalFunc0_0 arg0@@137))
)))
(assert (forall ((|#$R@@24| T@U) ) (!  (=> (= (type |#$R@@24|) TyType) (= (Tclass._System.___hTotalFunc0_0 (Tclass._System.___hTotalFunc0 |#$R@@24|)) |#$R@@24|))
 :qid |unknown.0:0|
 :skolemid |721|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@24|))
)))
(assert (forall ((|#$R@@25| T@U) (bx@@49 T@U) ) (!  (=> (and (and (= (type |#$R@@25|) TyType) (= (type bx@@49) BoxType)) ($IsBox bx@@49 (Tclass._System.___hTotalFunc0 |#$R@@25|))) (and (= ($Box ($Unbox HandleTypeType bx@@49)) bx@@49) ($Is ($Unbox HandleTypeType bx@@49) (Tclass._System.___hTotalFunc0 |#$R@@25|))))
 :qid |unknown.0:0|
 :skolemid |722|
 :pattern ( ($IsBox bx@@49 (Tclass._System.___hTotalFunc0 |#$R@@25|)))
)))
(assert (forall ((|#$R@@26| T@U) (|f#0@@5| T@U) ) (!  (=> (and (= (type |#$R@@26|) TyType) (= (type |f#0@@5|) HandleTypeType)) (and (=> ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|)) (and ($Is |f#0@@5| (Tclass._System.___hPartialFunc0 |#$R@@26|)) (Requires0 |#$R@@26| $OneHeap |f#0@@5|))) (=> (and ($Is |f#0@@5| (Tclass._System.___hPartialFunc0 |#$R@@26|)) (Requires0 |#$R@@26| $OneHeap |f#0@@5|)) ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|)))))
 :qid |unknown.0:0|
 :skolemid |723|
 :pattern ( ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|)))
)))
(assert (forall ((|#$R@@27| T@U) (|f#0@@6| T@U) ($h@@10 T@U) ) (!  (=> (and (and (= (type |#$R@@27|) TyType) (= (type |f#0@@6|) HandleTypeType)) (= (type $h@@10) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10) ($IsAlloc |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|) $h@@10)) (=> ($IsAlloc |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|) $h@@10) ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10))))
 :qid |unknown.0:0|
 :skolemid |724|
 :pattern ( ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10))
)))
(assert (forall ((arg0@@138 T@U) (arg1@@61 T@U) (arg2@@19 T@U) ) (! (= (type (Tclass._System.___hFunc2 arg0@@138 arg1@@61 arg2@@19)) TyType)
 :qid |funType:Tclass._System.___hFunc2|
 :pattern ( (Tclass._System.___hFunc2 arg0@@138 arg1@@61 arg2@@19))
)))
(assert (forall ((|#$T0@@15| T@U) (|#$T1| T@U) (|#$R@@28| T@U) ) (!  (=> (and (and (= (type |#$T0@@15|) TyType) (= (type |#$T1|) TyType)) (= (type |#$R@@28|) TyType)) (= (Tag (Tclass._System.___hFunc2 |#$T0@@15| |#$T1| |#$R@@28|)) Tagclass._System.___hFunc2))
 :qid |unknown.0:0|
 :skolemid |725|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@15| |#$T1| |#$R@@28|))
)))
(assert (forall ((arg0@@139 T@U) ) (! (= (type (Tclass._System.___hFunc2_0 arg0@@139)) TyType)
 :qid |funType:Tclass._System.___hFunc2_0|
 :pattern ( (Tclass._System.___hFunc2_0 arg0@@139))
)))
(assert (forall ((|#$T0@@16| T@U) (|#$T1@@0| T@U) (|#$R@@29| T@U) ) (!  (=> (and (and (= (type |#$T0@@16|) TyType) (= (type |#$T1@@0|) TyType)) (= (type |#$R@@29|) TyType)) (= (Tclass._System.___hFunc2_0 (Tclass._System.___hFunc2 |#$T0@@16| |#$T1@@0| |#$R@@29|)) |#$T0@@16|))
 :qid |unknown.0:0|
 :skolemid |726|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@16| |#$T1@@0| |#$R@@29|))
)))
(assert (forall ((arg0@@140 T@U) ) (! (= (type (Tclass._System.___hFunc2_1 arg0@@140)) TyType)
 :qid |funType:Tclass._System.___hFunc2_1|
 :pattern ( (Tclass._System.___hFunc2_1 arg0@@140))
)))
(assert (forall ((|#$T0@@17| T@U) (|#$T1@@1| T@U) (|#$R@@30| T@U) ) (!  (=> (and (and (= (type |#$T0@@17|) TyType) (= (type |#$T1@@1|) TyType)) (= (type |#$R@@30|) TyType)) (= (Tclass._System.___hFunc2_1 (Tclass._System.___hFunc2 |#$T0@@17| |#$T1@@1| |#$R@@30|)) |#$T1@@1|))
 :qid |unknown.0:0|
 :skolemid |727|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@17| |#$T1@@1| |#$R@@30|))
)))
(assert (forall ((arg0@@141 T@U) ) (! (= (type (Tclass._System.___hFunc2_2 arg0@@141)) TyType)
 :qid |funType:Tclass._System.___hFunc2_2|
 :pattern ( (Tclass._System.___hFunc2_2 arg0@@141))
)))
(assert (forall ((|#$T0@@18| T@U) (|#$T1@@2| T@U) (|#$R@@31| T@U) ) (!  (=> (and (and (= (type |#$T0@@18|) TyType) (= (type |#$T1@@2|) TyType)) (= (type |#$R@@31|) TyType)) (= (Tclass._System.___hFunc2_2 (Tclass._System.___hFunc2 |#$T0@@18| |#$T1@@2| |#$R@@31|)) |#$R@@31|))
 :qid |unknown.0:0|
 :skolemid |728|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@18| |#$T1@@2| |#$R@@31|))
)))
(assert (forall ((|#$T0@@19| T@U) (|#$T1@@3| T@U) (|#$R@@32| T@U) (bx@@50 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@19|) TyType) (= (type |#$T1@@3|) TyType)) (= (type |#$R@@32|) TyType)) (= (type bx@@50) BoxType)) ($IsBox bx@@50 (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|))) (and (= ($Box ($Unbox HandleTypeType bx@@50)) bx@@50) ($Is ($Unbox HandleTypeType bx@@50) (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|))))
 :qid |unknown.0:0|
 :skolemid |729|
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
 :skolemid |730|
 :pattern ( (Apply2 t0@@42 t1@@18 t2 heap@@11 (Handle2 h@@34 r@@16 rd@@5) bx0@@15 bx1))
)))
(assert (forall ((t0@@43 T@U) (t1@@19 T@U) (t2@@0 T@U) (heap@@12 T@U) (h@@35 T@U) (r@@17 T@U) (rd@@6 T@U) (bx0@@16 T@U) (bx1@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@43) TyType) (= (type t1@@19) TyType)) (= (type t2@@0) TyType)) (= (type heap@@12) (MapType0Type refType MapType1Type))) (= (type h@@35) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@17) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@6) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@16) BoxType)) (= (type bx1@@0) BoxType)) (U_2_bool (MapType3Select r@@17 heap@@12 bx0@@16 bx1@@0))) (Requires2 t0@@43 t1@@19 t2@@0 heap@@12 (Handle2 h@@35 r@@17 rd@@6) bx0@@16 bx1@@0))
 :qid |unknown.0:0|
 :skolemid |731|
 :pattern ( (Requires2 t0@@43 t1@@19 t2@@0 heap@@12 (Handle2 h@@35 r@@17 rd@@6) bx0@@16 bx1@@0))
)))
(assert (forall ((arg0@@151 T@U) (arg1@@71 T@U) (arg2@@29 T@U) (arg3@@11 T@U) (arg4@@3 T@U) (arg5@@0 T@U) (arg6@@0 T@U) ) (! (= (type (Reads2 arg0@@151 arg1@@71 arg2@@29 arg3@@11 arg4@@3 arg5@@0 arg6@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads2|
 :pattern ( (Reads2 arg0@@151 arg1@@71 arg2@@29 arg3@@11 arg4@@3 arg5@@0 arg6@@0))
)))
(assert (forall ((t0@@44 T@U) (t1@@20 T@U) (t2@@1 T@U) (heap@@13 T@U) (h@@36 T@U) (r@@18 T@U) (rd@@7 T@U) (bx0@@17 T@U) (bx1@@1 T@U) (bx@@51 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@44) TyType) (= (type t1@@20) TyType)) (= (type t2@@1) TyType)) (= (type heap@@13) (MapType0Type refType MapType1Type))) (= (type h@@36) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@18) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@7) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@17) BoxType)) (= (type bx1@@1) BoxType)) (= (type bx@@51) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads2 t0@@44 t1@@20 t2@@1 heap@@13 (Handle2 h@@36 r@@18 rd@@7) bx0@@17 bx1@@1) bx@@51)) (U_2_bool (MapType0Select (MapType3Select rd@@7 heap@@13 bx0@@17 bx1@@1) bx@@51))) (=> (U_2_bool (MapType0Select (MapType3Select rd@@7 heap@@13 bx0@@17 bx1@@1) bx@@51)) (U_2_bool (MapType0Select (Reads2 t0@@44 t1@@20 t2@@1 heap@@13 (Handle2 h@@36 r@@18 rd@@7) bx0@@17 bx1@@1) bx@@51)))))
 :qid |unknown.0:0|
 :skolemid |732|
 :pattern ( (MapType0Select (Reads2 t0@@44 t1@@20 t2@@1 heap@@13 (Handle2 h@@36 r@@18 rd@@7) bx0@@17 bx1@@1) bx@@51))
)))
(assert (forall ((t0@@45 T@U) (t1@@21 T@U) (t2@@2 T@U) (h0@@12 T@U) (h1@@12 T@U) (f@@29 T@U) (bx0@@18 T@U) (bx1@@2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@45) TyType) (= (type t1@@21) TyType)) (= (type t2@@2) TyType)) (= (type h0@@12) (MapType0Type refType MapType1Type))) (= (type h1@@12) (MapType0Type refType MapType1Type))) (= (type f@@29) HandleTypeType)) (= (type bx0@@18) BoxType)) (= (type bx1@@2) BoxType)) (and (and (and ($HeapSucc h0@@12 h1@@12) (and ($IsGoodHeap h0@@12) ($IsGoodHeap h1@@12))) (and (and ($IsBox bx0@@18 t0@@45) ($IsBox bx1@@2 t1@@21)) ($Is f@@29 (Tclass._System.___hFunc2 t0@@45 t1@@21 t2@@2)))) (forall ((o@@66 T@U) (fld@@11 T@U) ) (! (let ((a@@91 (FieldTypeInv0 (type fld@@11))))
 (=> (and (and (= (type o@@66) refType) (= (type fld@@11) (FieldType a@@91))) (and (not (= o@@66 null)) (U_2_bool (MapType0Select (Reads2 t0@@45 t1@@21 t2@@2 h0@@12 f@@29 bx0@@18 bx1@@2) ($Box o@@66))))) (= (MapType1Select (MapType0Select h0@@12 o@@66) fld@@11) (MapType1Select (MapType0Select h1@@12 o@@66) fld@@11))))
 :qid |unknown.0:0|
 :skolemid |733|
 :no-pattern (type o@@66)
 :no-pattern (type fld@@11)
 :no-pattern (U_2_int o@@66)
 :no-pattern (U_2_bool o@@66)
 :no-pattern (U_2_int fld@@11)
 :no-pattern (U_2_bool fld@@11)
)))) (= (Reads2 t0@@45 t1@@21 t2@@2 h0@@12 f@@29 bx0@@18 bx1@@2) (Reads2 t0@@45 t1@@21 t2@@2 h1@@12 f@@29 bx0@@18 bx1@@2)))
 :qid |unknown.0:0|
 :skolemid |734|
 :pattern ( ($HeapSucc h0@@12 h1@@12) (Reads2 t0@@45 t1@@21 t2@@2 h1@@12 f@@29 bx0@@18 bx1@@2))
)))
(assert (forall ((t0@@46 T@U) (t1@@22 T@U) (t2@@3 T@U) (h0@@13 T@U) (h1@@13 T@U) (f@@30 T@U) (bx0@@19 T@U) (bx1@@3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@46) TyType) (= (type t1@@22) TyType)) (= (type t2@@3) TyType)) (= (type h0@@13) (MapType0Type refType MapType1Type))) (= (type h1@@13) (MapType0Type refType MapType1Type))) (= (type f@@30) HandleTypeType)) (= (type bx0@@19) BoxType)) (= (type bx1@@3) BoxType)) (and (and (and ($HeapSucc h0@@13 h1@@13) (and ($IsGoodHeap h0@@13) ($IsGoodHeap h1@@13))) (and (and ($IsBox bx0@@19 t0@@46) ($IsBox bx1@@3 t1@@22)) ($Is f@@30 (Tclass._System.___hFunc2 t0@@46 t1@@22 t2@@3)))) (forall ((o@@67 T@U) (fld@@12 T@U) ) (! (let ((a@@92 (FieldTypeInv0 (type fld@@12))))
 (=> (and (and (= (type o@@67) refType) (= (type fld@@12) (FieldType a@@92))) (and (not (= o@@67 null)) (U_2_bool (MapType0Select (Reads2 t0@@46 t1@@22 t2@@3 h1@@13 f@@30 bx0@@19 bx1@@3) ($Box o@@67))))) (= (MapType1Select (MapType0Select h0@@13 o@@67) fld@@12) (MapType1Select (MapType0Select h1@@13 o@@67) fld@@12))))
 :qid |unknown.0:0|
 :skolemid |735|
 :no-pattern (type o@@67)
 :no-pattern (type fld@@12)
 :no-pattern (U_2_int o@@67)
 :no-pattern (U_2_bool o@@67)
 :no-pattern (U_2_int fld@@12)
 :no-pattern (U_2_bool fld@@12)
)))) (= (Reads2 t0@@46 t1@@22 t2@@3 h0@@13 f@@30 bx0@@19 bx1@@3) (Reads2 t0@@46 t1@@22 t2@@3 h1@@13 f@@30 bx0@@19 bx1@@3)))
 :qid |unknown.0:0|
 :skolemid |736|
 :pattern ( ($HeapSucc h0@@13 h1@@13) (Reads2 t0@@46 t1@@22 t2@@3 h1@@13 f@@30 bx0@@19 bx1@@3))
)))
(assert (forall ((t0@@47 T@U) (t1@@23 T@U) (t2@@4 T@U) (h0@@14 T@U) (h1@@14 T@U) (f@@31 T@U) (bx0@@20 T@U) (bx1@@4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@47) TyType) (= (type t1@@23) TyType)) (= (type t2@@4) TyType)) (= (type h0@@14) (MapType0Type refType MapType1Type))) (= (type h1@@14) (MapType0Type refType MapType1Type))) (= (type f@@31) HandleTypeType)) (= (type bx0@@20) BoxType)) (= (type bx1@@4) BoxType)) (and (and (and ($HeapSucc h0@@14 h1@@14) (and ($IsGoodHeap h0@@14) ($IsGoodHeap h1@@14))) (and (and ($IsBox bx0@@20 t0@@47) ($IsBox bx1@@4 t1@@23)) ($Is f@@31 (Tclass._System.___hFunc2 t0@@47 t1@@23 t2@@4)))) (forall ((o@@68 T@U) (fld@@13 T@U) ) (! (let ((a@@93 (FieldTypeInv0 (type fld@@13))))
 (=> (and (and (= (type o@@68) refType) (= (type fld@@13) (FieldType a@@93))) (and (not (= o@@68 null)) (U_2_bool (MapType0Select (Reads2 t0@@47 t1@@23 t2@@4 h0@@14 f@@31 bx0@@20 bx1@@4) ($Box o@@68))))) (= (MapType1Select (MapType0Select h0@@14 o@@68) fld@@13) (MapType1Select (MapType0Select h1@@14 o@@68) fld@@13))))
 :qid |unknown.0:0|
 :skolemid |737|
 :no-pattern (type o@@68)
 :no-pattern (type fld@@13)
 :no-pattern (U_2_int o@@68)
 :no-pattern (U_2_bool o@@68)
 :no-pattern (U_2_int fld@@13)
 :no-pattern (U_2_bool fld@@13)
)))) (and (=> (Requires2 t0@@47 t1@@23 t2@@4 h0@@14 f@@31 bx0@@20 bx1@@4) (Requires2 t0@@47 t1@@23 t2@@4 h1@@14 f@@31 bx0@@20 bx1@@4)) (=> (Requires2 t0@@47 t1@@23 t2@@4 h1@@14 f@@31 bx0@@20 bx1@@4) (Requires2 t0@@47 t1@@23 t2@@4 h0@@14 f@@31 bx0@@20 bx1@@4))))
 :qid |unknown.0:0|
 :skolemid |738|
 :pattern ( ($HeapSucc h0@@14 h1@@14) (Requires2 t0@@47 t1@@23 t2@@4 h1@@14 f@@31 bx0@@20 bx1@@4))
)))
(assert (forall ((t0@@48 T@U) (t1@@24 T@U) (t2@@5 T@U) (h0@@15 T@U) (h1@@15 T@U) (f@@32 T@U) (bx0@@21 T@U) (bx1@@5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@48) TyType) (= (type t1@@24) TyType)) (= (type t2@@5) TyType)) (= (type h0@@15) (MapType0Type refType MapType1Type))) (= (type h1@@15) (MapType0Type refType MapType1Type))) (= (type f@@32) HandleTypeType)) (= (type bx0@@21) BoxType)) (= (type bx1@@5) BoxType)) (and (and (and ($HeapSucc h0@@15 h1@@15) (and ($IsGoodHeap h0@@15) ($IsGoodHeap h1@@15))) (and (and ($IsBox bx0@@21 t0@@48) ($IsBox bx1@@5 t1@@24)) ($Is f@@32 (Tclass._System.___hFunc2 t0@@48 t1@@24 t2@@5)))) (forall ((o@@69 T@U) (fld@@14 T@U) ) (! (let ((a@@94 (FieldTypeInv0 (type fld@@14))))
 (=> (and (and (= (type o@@69) refType) (= (type fld@@14) (FieldType a@@94))) (and (not (= o@@69 null)) (U_2_bool (MapType0Select (Reads2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5) ($Box o@@69))))) (= (MapType1Select (MapType0Select h0@@15 o@@69) fld@@14) (MapType1Select (MapType0Select h1@@15 o@@69) fld@@14))))
 :qid |unknown.0:0|
 :skolemid |739|
 :no-pattern (type o@@69)
 :no-pattern (type fld@@14)
 :no-pattern (U_2_int o@@69)
 :no-pattern (U_2_bool o@@69)
 :no-pattern (U_2_int fld@@14)
 :no-pattern (U_2_bool fld@@14)
)))) (and (=> (Requires2 t0@@48 t1@@24 t2@@5 h0@@15 f@@32 bx0@@21 bx1@@5) (Requires2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5)) (=> (Requires2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5) (Requires2 t0@@48 t1@@24 t2@@5 h0@@15 f@@32 bx0@@21 bx1@@5))))
 :qid |unknown.0:0|
 :skolemid |740|
 :pattern ( ($HeapSucc h0@@15 h1@@15) (Requires2 t0@@48 t1@@24 t2@@5 h1@@15 f@@32 bx0@@21 bx1@@5))
)))
(assert (forall ((t0@@49 T@U) (t1@@25 T@U) (t2@@6 T@U) (h0@@16 T@U) (h1@@16 T@U) (f@@33 T@U) (bx0@@22 T@U) (bx1@@6 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@49) TyType) (= (type t1@@25) TyType)) (= (type t2@@6) TyType)) (= (type h0@@16) (MapType0Type refType MapType1Type))) (= (type h1@@16) (MapType0Type refType MapType1Type))) (= (type f@@33) HandleTypeType)) (= (type bx0@@22) BoxType)) (= (type bx1@@6) BoxType)) (and (and (and ($HeapSucc h0@@16 h1@@16) (and ($IsGoodHeap h0@@16) ($IsGoodHeap h1@@16))) (and (and ($IsBox bx0@@22 t0@@49) ($IsBox bx1@@6 t1@@25)) ($Is f@@33 (Tclass._System.___hFunc2 t0@@49 t1@@25 t2@@6)))) (forall ((o@@70 T@U) (fld@@15 T@U) ) (! (let ((a@@95 (FieldTypeInv0 (type fld@@15))))
 (=> (and (and (= (type o@@70) refType) (= (type fld@@15) (FieldType a@@95))) (and (not (= o@@70 null)) (U_2_bool (MapType0Select (Reads2 t0@@49 t1@@25 t2@@6 h0@@16 f@@33 bx0@@22 bx1@@6) ($Box o@@70))))) (= (MapType1Select (MapType0Select h0@@16 o@@70) fld@@15) (MapType1Select (MapType0Select h1@@16 o@@70) fld@@15))))
 :qid |unknown.0:0|
 :skolemid |741|
 :no-pattern (type o@@70)
 :no-pattern (type fld@@15)
 :no-pattern (U_2_int o@@70)
 :no-pattern (U_2_bool o@@70)
 :no-pattern (U_2_int fld@@15)
 :no-pattern (U_2_bool fld@@15)
)))) (= (Apply2 t0@@49 t1@@25 t2@@6 h0@@16 f@@33 bx0@@22 bx1@@6) (Apply2 t0@@49 t1@@25 t2@@6 h1@@16 f@@33 bx0@@22 bx1@@6)))
 :qid |unknown.0:0|
 :skolemid |742|
 :pattern ( ($HeapSucc h0@@16 h1@@16) (Apply2 t0@@49 t1@@25 t2@@6 h1@@16 f@@33 bx0@@22 bx1@@6))
)))
(assert (forall ((t0@@50 T@U) (t1@@26 T@U) (t2@@7 T@U) (h0@@17 T@U) (h1@@17 T@U) (f@@34 T@U) (bx0@@23 T@U) (bx1@@7 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@50) TyType) (= (type t1@@26) TyType)) (= (type t2@@7) TyType)) (= (type h0@@17) (MapType0Type refType MapType1Type))) (= (type h1@@17) (MapType0Type refType MapType1Type))) (= (type f@@34) HandleTypeType)) (= (type bx0@@23) BoxType)) (= (type bx1@@7) BoxType)) (and (and (and ($HeapSucc h0@@17 h1@@17) (and ($IsGoodHeap h0@@17) ($IsGoodHeap h1@@17))) (and (and ($IsBox bx0@@23 t0@@50) ($IsBox bx1@@7 t1@@26)) ($Is f@@34 (Tclass._System.___hFunc2 t0@@50 t1@@26 t2@@7)))) (forall ((o@@71 T@U) (fld@@16 T@U) ) (! (let ((a@@96 (FieldTypeInv0 (type fld@@16))))
 (=> (and (and (= (type o@@71) refType) (= (type fld@@16) (FieldType a@@96))) (and (not (= o@@71 null)) (U_2_bool (MapType0Select (Reads2 t0@@50 t1@@26 t2@@7 h1@@17 f@@34 bx0@@23 bx1@@7) ($Box o@@71))))) (= (MapType1Select (MapType0Select h0@@17 o@@71) fld@@16) (MapType1Select (MapType0Select h1@@17 o@@71) fld@@16))))
 :qid |unknown.0:0|
 :skolemid |743|
 :no-pattern (type o@@71)
 :no-pattern (type fld@@16)
 :no-pattern (U_2_int o@@71)
 :no-pattern (U_2_bool o@@71)
 :no-pattern (U_2_int fld@@16)
 :no-pattern (U_2_bool fld@@16)
)))) (= (Apply2 t0@@50 t1@@26 t2@@7 h0@@17 f@@34 bx0@@23 bx1@@7) (Apply2 t0@@50 t1@@26 t2@@7 h1@@17 f@@34 bx0@@23 bx1@@7)))
 :qid |unknown.0:0|
 :skolemid |744|
 :pattern ( ($HeapSucc h0@@17 h1@@17) (Apply2 t0@@50 t1@@26 t2@@7 h1@@17 f@@34 bx0@@23 bx1@@7))
)))
(assert (forall ((t0@@51 T@U) (t1@@27 T@U) (t2@@8 T@U) (heap@@14 T@U) (f@@35 T@U) (bx0@@24 T@U) (bx1@@8 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@51) TyType) (= (type t1@@27) TyType)) (= (type t2@@8) TyType)) (= (type heap@@14) (MapType0Type refType MapType1Type))) (= (type f@@35) HandleTypeType)) (= (type bx0@@24) BoxType)) (= (type bx1@@8) BoxType)) (and ($IsGoodHeap heap@@14) (and (and ($IsBox bx0@@24 t0@@51) ($IsBox bx1@@8 t1@@27)) ($Is f@@35 (Tclass._System.___hFunc2 t0@@51 t1@@27 t2@@8))))) (and (=> (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 $OneHeap f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 heap@@14 f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 heap@@14 f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads2 t0@@51 t1@@27 t2@@8 $OneHeap f@@35 bx0@@24 bx1@@8) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |745|
 :pattern ( (Reads2 t0@@51 t1@@27 t2@@8 $OneHeap f@@35 bx0@@24 bx1@@8) ($IsGoodHeap heap@@14))
 :pattern ( (Reads2 t0@@51 t1@@27 t2@@8 heap@@14 f@@35 bx0@@24 bx1@@8))
)))
(assert (forall ((t0@@52 T@U) (t1@@28 T@U) (t2@@9 T@U) (heap@@15 T@U) (f@@36 T@U) (bx0@@25 T@U) (bx1@@9 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@52) TyType) (= (type t1@@28) TyType)) (= (type t2@@9) TyType)) (= (type heap@@15) (MapType0Type refType MapType1Type))) (= (type f@@36) HandleTypeType)) (= (type bx0@@25) BoxType)) (= (type bx1@@9) BoxType)) (and (and ($IsGoodHeap heap@@15) (and (and ($IsBox bx0@@25 t0@@52) ($IsBox bx1@@9 t1@@28)) ($Is f@@36 (Tclass._System.___hFunc2 t0@@52 t1@@28 t2@@9)))) (|Set#Equal| (Reads2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9) (|Set#Empty| BoxType)))) (and (=> (Requires2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9) (Requires2 t0@@52 t1@@28 t2@@9 heap@@15 f@@36 bx0@@25 bx1@@9)) (=> (Requires2 t0@@52 t1@@28 t2@@9 heap@@15 f@@36 bx0@@25 bx1@@9) (Requires2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9))))
 :qid |unknown.0:0|
 :skolemid |746|
 :pattern ( (Requires2 t0@@52 t1@@28 t2@@9 $OneHeap f@@36 bx0@@25 bx1@@9) ($IsGoodHeap heap@@15))
 :pattern ( (Requires2 t0@@52 t1@@28 t2@@9 heap@@15 f@@36 bx0@@25 bx1@@9))
)))
(assert (forall ((f@@37 T@U) (t0@@53 T@U) (t1@@29 T@U) (t2@@10 T@U) ) (!  (=> (and (and (and (= (type f@@37) HandleTypeType) (= (type t0@@53) TyType)) (= (type t1@@29) TyType)) (= (type t2@@10) TyType)) (and (=> ($Is f@@37 (Tclass._System.___hFunc2 t0@@53 t1@@29 t2@@10)) (forall ((h@@37 T@U) (bx0@@26 T@U) (bx1@@10 T@U) ) (!  (=> (and (and (and (= (type h@@37) (MapType0Type refType MapType1Type)) (= (type bx0@@26) BoxType)) (= (type bx1@@10) BoxType)) (and (and ($IsGoodHeap h@@37) (and ($IsBox bx0@@26 t0@@53) ($IsBox bx1@@10 t1@@29))) (Requires2 t0@@53 t1@@29 t2@@10 h@@37 f@@37 bx0@@26 bx1@@10))) ($IsBox (Apply2 t0@@53 t1@@29 t2@@10 h@@37 f@@37 bx0@@26 bx1@@10) t2@@10))
 :qid |DafnyPre.515:12|
 :skolemid |747|
 :pattern ( (Apply2 t0@@53 t1@@29 t2@@10 h@@37 f@@37 bx0@@26 bx1@@10))
))) (=> (forall ((h@@38 T@U) (bx0@@27 T@U) (bx1@@11 T@U) ) (!  (=> (and (and (and (= (type h@@38) (MapType0Type refType MapType1Type)) (= (type bx0@@27) BoxType)) (= (type bx1@@11) BoxType)) (and (and ($IsGoodHeap h@@38) (and ($IsBox bx0@@27 t0@@53) ($IsBox bx1@@11 t1@@29))) (Requires2 t0@@53 t1@@29 t2@@10 h@@38 f@@37 bx0@@27 bx1@@11))) ($IsBox (Apply2 t0@@53 t1@@29 t2@@10 h@@38 f@@37 bx0@@27 bx1@@11) t2@@10))
 :qid |DafnyPre.515:12|
 :skolemid |747|
 :pattern ( (Apply2 t0@@53 t1@@29 t2@@10 h@@38 f@@37 bx0@@27 bx1@@11))
)) ($Is f@@37 (Tclass._System.___hFunc2 t0@@53 t1@@29 t2@@10)))))
 :qid |unknown.0:0|
 :skolemid |748|
 :pattern ( ($Is f@@37 (Tclass._System.___hFunc2 t0@@53 t1@@29 t2@@10)))
)))
(assert (forall ((f@@38 T@U) (t0@@54 T@U) (t1@@30 T@U) (t2@@11 T@U) (u0@@1 T@U) (u1@@0 T@U) (u2 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type f@@38) HandleTypeType) (= (type t0@@54) TyType)) (= (type t1@@30) TyType)) (= (type t2@@11) TyType)) (= (type u0@@1) TyType)) (= (type u1@@0) TyType)) (= (type u2) TyType)) (and (and (and ($Is f@@38 (Tclass._System.___hFunc2 t0@@54 t1@@30 t2@@11)) (forall ((bx@@52 T@U) ) (!  (=> (and (= (type bx@@52) BoxType) ($IsBox bx@@52 u0@@1)) ($IsBox bx@@52 t0@@54))
 :qid |unknown.0:0|
 :skolemid |749|
 :pattern ( ($IsBox bx@@52 u0@@1))
 :pattern ( ($IsBox bx@@52 t0@@54))
))) (forall ((bx@@53 T@U) ) (!  (=> (and (= (type bx@@53) BoxType) ($IsBox bx@@53 u1@@0)) ($IsBox bx@@53 t1@@30))
 :qid |unknown.0:0|
 :skolemid |750|
 :pattern ( ($IsBox bx@@53 u1@@0))
 :pattern ( ($IsBox bx@@53 t1@@30))
))) (forall ((bx@@54 T@U) ) (!  (=> (and (= (type bx@@54) BoxType) ($IsBox bx@@54 t2@@11)) ($IsBox bx@@54 u2))
 :qid |unknown.0:0|
 :skolemid |751|
 :pattern ( ($IsBox bx@@54 t2@@11))
 :pattern ( ($IsBox bx@@54 u2))
)))) ($Is f@@38 (Tclass._System.___hFunc2 u0@@1 u1@@0 u2)))
 :qid |unknown.0:0|
 :skolemid |752|
 :pattern ( ($Is f@@38 (Tclass._System.___hFunc2 t0@@54 t1@@30 t2@@11)) ($Is f@@38 (Tclass._System.___hFunc2 u0@@1 u1@@0 u2)))
)))
(assert (forall ((f@@39 T@U) (t0@@55 T@U) (t1@@31 T@U) (t2@@12 T@U) (h@@39 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@39) HandleTypeType) (= (type t0@@55) TyType)) (= (type t1@@31) TyType)) (= (type t2@@12) TyType)) (= (type h@@39) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@39)) (and (=> ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@55 t1@@31 t2@@12) h@@39) (forall ((bx0@@28 T@U) (bx1@@12 T@U) ) (!  (=> (and (= (type bx0@@28) BoxType) (= (type bx1@@12) BoxType)) (=> (and (and (and ($IsBox bx0@@28 t0@@55) ($IsAllocBox bx0@@28 t0@@55 h@@39)) (and ($IsBox bx1@@12 t1@@31) ($IsAllocBox bx1@@12 t1@@31 h@@39))) (Requires2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12)) (forall ((r@@19 T@U) ) (!  (=> (= (type r@@19) refType) (=> (and (not (= r@@19 null)) (U_2_bool (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12) ($Box r@@19)))) (U_2_bool (MapType1Select (MapType0Select h@@39 r@@19) alloc))))
 :qid |unknown.0:0|
 :skolemid |753|
 :pattern ( (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12) ($Box r@@19)))
))))
 :qid |unknown.0:0|
 :skolemid |754|
 :pattern ( (Apply2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12))
 :pattern ( (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@28 bx1@@12))
))) (=> (forall ((bx0@@29 T@U) (bx1@@13 T@U) ) (!  (=> (and (= (type bx0@@29) BoxType) (= (type bx1@@13) BoxType)) (=> (and (and (and ($IsBox bx0@@29 t0@@55) ($IsAllocBox bx0@@29 t0@@55 h@@39)) (and ($IsBox bx1@@13 t1@@31) ($IsAllocBox bx1@@13 t1@@31 h@@39))) (Requires2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13)) (forall ((r@@20 T@U) ) (!  (=> (= (type r@@20) refType) (=> (and (not (= r@@20 null)) (U_2_bool (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13) ($Box r@@20)))) (U_2_bool (MapType1Select (MapType0Select h@@39 r@@20) alloc))))
 :qid |unknown.0:0|
 :skolemid |753|
 :pattern ( (MapType0Select (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13) ($Box r@@20)))
))))
 :qid |unknown.0:0|
 :skolemid |754|
 :pattern ( (Apply2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13))
 :pattern ( (Reads2 t0@@55 t1@@31 t2@@12 h@@39 f@@39 bx0@@29 bx1@@13))
)) ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@55 t1@@31 t2@@12) h@@39))))
 :qid |unknown.0:0|
 :skolemid |755|
 :pattern ( ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@55 t1@@31 t2@@12) h@@39))
)))
(assert (forall ((f@@40 T@U) (t0@@56 T@U) (t1@@32 T@U) (t2@@13 T@U) (h@@40 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@40) HandleTypeType) (= (type t0@@56) TyType)) (= (type t1@@32) TyType)) (= (type t2@@13) TyType)) (= (type h@@40) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@40) ($IsAlloc f@@40 (Tclass._System.___hFunc2 t0@@56 t1@@32 t2@@13) h@@40))) (forall ((bx0@@30 T@U) (bx1@@14 T@U) ) (!  (=> (and (= (type bx0@@30) BoxType) (= (type bx1@@14) BoxType)) (=> (and (and ($IsAllocBox bx0@@30 t0@@56 h@@40) ($IsAllocBox bx1@@14 t1@@32 h@@40)) (Requires2 t0@@56 t1@@32 t2@@13 h@@40 f@@40 bx0@@30 bx1@@14)) ($IsAllocBox (Apply2 t0@@56 t1@@32 t2@@13 h@@40 f@@40 bx0@@30 bx1@@14) t2@@13 h@@40)))
 :qid |unknown.0:0|
 :skolemid |756|
 :pattern ( (Apply2 t0@@56 t1@@32 t2@@13 h@@40 f@@40 bx0@@30 bx1@@14))
)))
 :qid |unknown.0:0|
 :skolemid |757|
 :pattern ( ($IsAlloc f@@40 (Tclass._System.___hFunc2 t0@@56 t1@@32 t2@@13) h@@40))
)))
(assert (forall ((arg0@@152 T@U) (arg1@@72 T@U) (arg2@@30 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2 arg0@@152 arg1@@72 arg2@@30)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2|
 :pattern ( (Tclass._System.___hPartialFunc2 arg0@@152 arg1@@72 arg2@@30))
)))
(assert (forall ((|#$T0@@20| T@U) (|#$T1@@4| T@U) (|#$R@@33| T@U) ) (!  (=> (and (and (= (type |#$T0@@20|) TyType) (= (type |#$T1@@4|) TyType)) (= (type |#$R@@33|) TyType)) (= (Tag (Tclass._System.___hPartialFunc2 |#$T0@@20| |#$T1@@4| |#$R@@33|)) Tagclass._System.___hPartialFunc2))
 :qid |unknown.0:0|
 :skolemid |758|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@20| |#$T1@@4| |#$R@@33|))
)))
(assert (forall ((arg0@@153 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_0 arg0@@153)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_0|
 :pattern ( (Tclass._System.___hPartialFunc2_0 arg0@@153))
)))
(assert (forall ((|#$T0@@21| T@U) (|#$T1@@5| T@U) (|#$R@@34| T@U) ) (!  (=> (and (and (= (type |#$T0@@21|) TyType) (= (type |#$T1@@5|) TyType)) (= (type |#$R@@34|) TyType)) (= (Tclass._System.___hPartialFunc2_0 (Tclass._System.___hPartialFunc2 |#$T0@@21| |#$T1@@5| |#$R@@34|)) |#$T0@@21|))
 :qid |unknown.0:0|
 :skolemid |759|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@21| |#$T1@@5| |#$R@@34|))
)))
(assert (forall ((arg0@@154 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_1 arg0@@154)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_1|
 :pattern ( (Tclass._System.___hPartialFunc2_1 arg0@@154))
)))
(assert (forall ((|#$T0@@22| T@U) (|#$T1@@6| T@U) (|#$R@@35| T@U) ) (!  (=> (and (and (= (type |#$T0@@22|) TyType) (= (type |#$T1@@6|) TyType)) (= (type |#$R@@35|) TyType)) (= (Tclass._System.___hPartialFunc2_1 (Tclass._System.___hPartialFunc2 |#$T0@@22| |#$T1@@6| |#$R@@35|)) |#$T1@@6|))
 :qid |unknown.0:0|
 :skolemid |760|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@22| |#$T1@@6| |#$R@@35|))
)))
(assert (forall ((arg0@@155 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_2 arg0@@155)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_2|
 :pattern ( (Tclass._System.___hPartialFunc2_2 arg0@@155))
)))
(assert (forall ((|#$T0@@23| T@U) (|#$T1@@7| T@U) (|#$R@@36| T@U) ) (!  (=> (and (and (= (type |#$T0@@23|) TyType) (= (type |#$T1@@7|) TyType)) (= (type |#$R@@36|) TyType)) (= (Tclass._System.___hPartialFunc2_2 (Tclass._System.___hPartialFunc2 |#$T0@@23| |#$T1@@7| |#$R@@36|)) |#$R@@36|))
 :qid |unknown.0:0|
 :skolemid |761|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@23| |#$T1@@7| |#$R@@36|))
)))
(assert (forall ((|#$T0@@24| T@U) (|#$T1@@8| T@U) (|#$R@@37| T@U) (bx@@55 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@24|) TyType) (= (type |#$T1@@8|) TyType)) (= (type |#$R@@37|) TyType)) (= (type bx@@55) BoxType)) ($IsBox bx@@55 (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|))) (and (= ($Box ($Unbox HandleTypeType bx@@55)) bx@@55) ($Is ($Unbox HandleTypeType bx@@55) (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|))))
 :qid |unknown.0:0|
 :skolemid |762|
 :pattern ( ($IsBox bx@@55 (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|)))
)))
(assert (forall ((|#$T0@@25| T@U) (|#$T1@@9| T@U) (|#$R@@38| T@U) (|f#0@@7| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@25|) TyType) (= (type |#$T1@@9|) TyType)) (= (type |#$R@@38|) TyType)) (= (type |f#0@@7|) HandleTypeType)) (and (=> ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)) (and ($Is |f#0@@7| (Tclass._System.___hFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)) (forall ((|x0#0@@3| T@U) (|x1#0| T@U) ) (!  (=> (and (and (= (type |x0#0@@3|) BoxType) (= (type |x1#0|) BoxType)) (and ($IsBox |x0#0@@3| |#$T0@@25|) ($IsBox |x1#0| |#$T1@@9|))) (|Set#Equal| (Reads2 |#$T0@@25| |#$T1@@9| |#$R@@38| $OneHeap |f#0@@7| |x0#0@@3| |x1#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |763|
 :no-pattern (type |x0#0@@3|)
 :no-pattern (type |x1#0|)
 :no-pattern (U_2_int |x0#0@@3|)
 :no-pattern (U_2_bool |x0#0@@3|)
 :no-pattern (U_2_int |x1#0|)
 :no-pattern (U_2_bool |x1#0|)
)))) (=> (and ($Is |f#0@@7| (Tclass._System.___hFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)) (forall ((|x0#0@@4| T@U) (|x1#0@@0| T@U) ) (!  (=> (and (and (= (type |x0#0@@4|) BoxType) (= (type |x1#0@@0|) BoxType)) (and ($IsBox |x0#0@@4| |#$T0@@25|) ($IsBox |x1#0@@0| |#$T1@@9|))) (|Set#Equal| (Reads2 |#$T0@@25| |#$T1@@9| |#$R@@38| $OneHeap |f#0@@7| |x0#0@@4| |x1#0@@0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |763|
 :no-pattern (type |x0#0@@4|)
 :no-pattern (type |x1#0@@0|)
 :no-pattern (U_2_int |x0#0@@4|)
 :no-pattern (U_2_bool |x0#0@@4|)
 :no-pattern (U_2_int |x1#0@@0|)
 :no-pattern (U_2_bool |x1#0@@0|)
))) ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)))))
 :qid |unknown.0:0|
 :skolemid |764|
 :pattern ( ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)))
)))
(assert (forall ((|#$T0@@26| T@U) (|#$T1@@10| T@U) (|#$R@@39| T@U) (|f#0@@8| T@U) ($h@@11 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@26|) TyType) (= (type |#$T1@@10|) TyType)) (= (type |#$R@@39|) TyType)) (= (type |f#0@@8|) HandleTypeType)) (= (type $h@@11) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11) ($IsAlloc |f#0@@8| (Tclass._System.___hFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11)) (=> ($IsAlloc |f#0@@8| (Tclass._System.___hFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11) ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11))))
 :qid |unknown.0:0|
 :skolemid |765|
 :pattern ( ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@11))
)))
(assert (forall ((arg0@@156 T@U) (arg1@@73 T@U) (arg2@@31 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2 arg0@@156 arg1@@73 arg2@@31)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2|
 :pattern ( (Tclass._System.___hTotalFunc2 arg0@@156 arg1@@73 arg2@@31))
)))
(assert (forall ((|#$T0@@27| T@U) (|#$T1@@11| T@U) (|#$R@@40| T@U) ) (!  (=> (and (and (= (type |#$T0@@27|) TyType) (= (type |#$T1@@11|) TyType)) (= (type |#$R@@40|) TyType)) (= (Tag (Tclass._System.___hTotalFunc2 |#$T0@@27| |#$T1@@11| |#$R@@40|)) Tagclass._System.___hTotalFunc2))
 :qid |unknown.0:0|
 :skolemid |766|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@27| |#$T1@@11| |#$R@@40|))
)))
(assert (forall ((arg0@@157 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_0 arg0@@157)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_0|
 :pattern ( (Tclass._System.___hTotalFunc2_0 arg0@@157))
)))
(assert (forall ((|#$T0@@28| T@U) (|#$T1@@12| T@U) (|#$R@@41| T@U) ) (!  (=> (and (and (= (type |#$T0@@28|) TyType) (= (type |#$T1@@12|) TyType)) (= (type |#$R@@41|) TyType)) (= (Tclass._System.___hTotalFunc2_0 (Tclass._System.___hTotalFunc2 |#$T0@@28| |#$T1@@12| |#$R@@41|)) |#$T0@@28|))
 :qid |unknown.0:0|
 :skolemid |767|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@28| |#$T1@@12| |#$R@@41|))
)))
(assert (forall ((arg0@@158 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_1 arg0@@158)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_1|
 :pattern ( (Tclass._System.___hTotalFunc2_1 arg0@@158))
)))
(assert (forall ((|#$T0@@29| T@U) (|#$T1@@13| T@U) (|#$R@@42| T@U) ) (!  (=> (and (and (= (type |#$T0@@29|) TyType) (= (type |#$T1@@13|) TyType)) (= (type |#$R@@42|) TyType)) (= (Tclass._System.___hTotalFunc2_1 (Tclass._System.___hTotalFunc2 |#$T0@@29| |#$T1@@13| |#$R@@42|)) |#$T1@@13|))
 :qid |unknown.0:0|
 :skolemid |768|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@29| |#$T1@@13| |#$R@@42|))
)))
(assert (forall ((arg0@@159 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_2 arg0@@159)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_2|
 :pattern ( (Tclass._System.___hTotalFunc2_2 arg0@@159))
)))
(assert (forall ((|#$T0@@30| T@U) (|#$T1@@14| T@U) (|#$R@@43| T@U) ) (!  (=> (and (and (= (type |#$T0@@30|) TyType) (= (type |#$T1@@14|) TyType)) (= (type |#$R@@43|) TyType)) (= (Tclass._System.___hTotalFunc2_2 (Tclass._System.___hTotalFunc2 |#$T0@@30| |#$T1@@14| |#$R@@43|)) |#$R@@43|))
 :qid |unknown.0:0|
 :skolemid |769|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@30| |#$T1@@14| |#$R@@43|))
)))
(assert (forall ((|#$T0@@31| T@U) (|#$T1@@15| T@U) (|#$R@@44| T@U) (bx@@56 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@31|) TyType) (= (type |#$T1@@15|) TyType)) (= (type |#$R@@44|) TyType)) (= (type bx@@56) BoxType)) ($IsBox bx@@56 (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|))) (and (= ($Box ($Unbox HandleTypeType bx@@56)) bx@@56) ($Is ($Unbox HandleTypeType bx@@56) (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|))))
 :qid |unknown.0:0|
 :skolemid |770|
 :pattern ( ($IsBox bx@@56 (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|)))
)))
(assert (forall ((|#$T0@@32| T@U) (|#$T1@@16| T@U) (|#$R@@45| T@U) (|f#0@@9| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@32|) TyType) (= (type |#$T1@@16|) TyType)) (= (type |#$R@@45|) TyType)) (= (type |f#0@@9|) HandleTypeType)) (and (=> ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)) (and ($Is |f#0@@9| (Tclass._System.___hPartialFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)) (forall ((|x0#0@@5| T@U) (|x1#0@@1| T@U) ) (!  (=> (and (and (= (type |x0#0@@5|) BoxType) (= (type |x1#0@@1|) BoxType)) (and ($IsBox |x0#0@@5| |#$T0@@32|) ($IsBox |x1#0@@1| |#$T1@@16|))) (Requires2 |#$T0@@32| |#$T1@@16| |#$R@@45| $OneHeap |f#0@@9| |x0#0@@5| |x1#0@@1|))
 :qid |unknown.0:0|
 :skolemid |771|
 :no-pattern (type |x0#0@@5|)
 :no-pattern (type |x1#0@@1|)
 :no-pattern (U_2_int |x0#0@@5|)
 :no-pattern (U_2_bool |x0#0@@5|)
 :no-pattern (U_2_int |x1#0@@1|)
 :no-pattern (U_2_bool |x1#0@@1|)
)))) (=> (and ($Is |f#0@@9| (Tclass._System.___hPartialFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)) (forall ((|x0#0@@6| T@U) (|x1#0@@2| T@U) ) (!  (=> (and (and (= (type |x0#0@@6|) BoxType) (= (type |x1#0@@2|) BoxType)) (and ($IsBox |x0#0@@6| |#$T0@@32|) ($IsBox |x1#0@@2| |#$T1@@16|))) (Requires2 |#$T0@@32| |#$T1@@16| |#$R@@45| $OneHeap |f#0@@9| |x0#0@@6| |x1#0@@2|))
 :qid |unknown.0:0|
 :skolemid |771|
 :no-pattern (type |x0#0@@6|)
 :no-pattern (type |x1#0@@2|)
 :no-pattern (U_2_int |x0#0@@6|)
 :no-pattern (U_2_bool |x0#0@@6|)
 :no-pattern (U_2_int |x1#0@@2|)
 :no-pattern (U_2_bool |x1#0@@2|)
))) ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)))))
 :qid |unknown.0:0|
 :skolemid |772|
 :pattern ( ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)))
)))
(assert (forall ((|#$T0@@33| T@U) (|#$T1@@17| T@U) (|#$R@@46| T@U) (|f#0@@10| T@U) ($h@@12 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@33|) TyType) (= (type |#$T1@@17|) TyType)) (= (type |#$R@@46|) TyType)) (= (type |f#0@@10|) HandleTypeType)) (= (type $h@@12) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12) ($IsAlloc |f#0@@10| (Tclass._System.___hPartialFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12)) (=> ($IsAlloc |f#0@@10| (Tclass._System.___hPartialFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12) ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12))))
 :qid |unknown.0:0|
 :skolemid |773|
 :pattern ( ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@12))
)))
(assert (forall ((arg0@@160 T@U) (arg1@@74 T@U) (arg2@@32 T@U) (arg3@@12 T@U) ) (! (= (type (Tclass._System.___hFunc3 arg0@@160 arg1@@74 arg2@@32 arg3@@12)) TyType)
 :qid |funType:Tclass._System.___hFunc3|
 :pattern ( (Tclass._System.___hFunc3 arg0@@160 arg1@@74 arg2@@32 arg3@@12))
)))
(assert (forall ((|#$T0@@34| T@U) (|#$T1@@18| T@U) (|#$T2| T@U) (|#$R@@47| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@34|) TyType) (= (type |#$T1@@18|) TyType)) (= (type |#$T2|) TyType)) (= (type |#$R@@47|) TyType)) (= (Tag (Tclass._System.___hFunc3 |#$T0@@34| |#$T1@@18| |#$T2| |#$R@@47|)) Tagclass._System.___hFunc3))
 :qid |unknown.0:0|
 :skolemid |774|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@34| |#$T1@@18| |#$T2| |#$R@@47|))
)))
(assert (forall ((arg0@@161 T@U) ) (! (= (type (Tclass._System.___hFunc3_0 arg0@@161)) TyType)
 :qid |funType:Tclass._System.___hFunc3_0|
 :pattern ( (Tclass._System.___hFunc3_0 arg0@@161))
)))
(assert (forall ((|#$T0@@35| T@U) (|#$T1@@19| T@U) (|#$T2@@0| T@U) (|#$R@@48| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@35|) TyType) (= (type |#$T1@@19|) TyType)) (= (type |#$T2@@0|) TyType)) (= (type |#$R@@48|) TyType)) (= (Tclass._System.___hFunc3_0 (Tclass._System.___hFunc3 |#$T0@@35| |#$T1@@19| |#$T2@@0| |#$R@@48|)) |#$T0@@35|))
 :qid |unknown.0:0|
 :skolemid |775|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@35| |#$T1@@19| |#$T2@@0| |#$R@@48|))
)))
(assert (forall ((arg0@@162 T@U) ) (! (= (type (Tclass._System.___hFunc3_1 arg0@@162)) TyType)
 :qid |funType:Tclass._System.___hFunc3_1|
 :pattern ( (Tclass._System.___hFunc3_1 arg0@@162))
)))
(assert (forall ((|#$T0@@36| T@U) (|#$T1@@20| T@U) (|#$T2@@1| T@U) (|#$R@@49| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@36|) TyType) (= (type |#$T1@@20|) TyType)) (= (type |#$T2@@1|) TyType)) (= (type |#$R@@49|) TyType)) (= (Tclass._System.___hFunc3_1 (Tclass._System.___hFunc3 |#$T0@@36| |#$T1@@20| |#$T2@@1| |#$R@@49|)) |#$T1@@20|))
 :qid |unknown.0:0|
 :skolemid |776|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@36| |#$T1@@20| |#$T2@@1| |#$R@@49|))
)))
(assert (forall ((arg0@@163 T@U) ) (! (= (type (Tclass._System.___hFunc3_2 arg0@@163)) TyType)
 :qid |funType:Tclass._System.___hFunc3_2|
 :pattern ( (Tclass._System.___hFunc3_2 arg0@@163))
)))
(assert (forall ((|#$T0@@37| T@U) (|#$T1@@21| T@U) (|#$T2@@2| T@U) (|#$R@@50| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@37|) TyType) (= (type |#$T1@@21|) TyType)) (= (type |#$T2@@2|) TyType)) (= (type |#$R@@50|) TyType)) (= (Tclass._System.___hFunc3_2 (Tclass._System.___hFunc3 |#$T0@@37| |#$T1@@21| |#$T2@@2| |#$R@@50|)) |#$T2@@2|))
 :qid |unknown.0:0|
 :skolemid |777|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@37| |#$T1@@21| |#$T2@@2| |#$R@@50|))
)))
(assert (forall ((arg0@@164 T@U) ) (! (= (type (Tclass._System.___hFunc3_3 arg0@@164)) TyType)
 :qid |funType:Tclass._System.___hFunc3_3|
 :pattern ( (Tclass._System.___hFunc3_3 arg0@@164))
)))
(assert (forall ((|#$T0@@38| T@U) (|#$T1@@22| T@U) (|#$T2@@3| T@U) (|#$R@@51| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@38|) TyType) (= (type |#$T1@@22|) TyType)) (= (type |#$T2@@3|) TyType)) (= (type |#$R@@51|) TyType)) (= (Tclass._System.___hFunc3_3 (Tclass._System.___hFunc3 |#$T0@@38| |#$T1@@22| |#$T2@@3| |#$R@@51|)) |#$R@@51|))
 :qid |unknown.0:0|
 :skolemid |778|
 :pattern ( (Tclass._System.___hFunc3 |#$T0@@38| |#$T1@@22| |#$T2@@3| |#$R@@51|))
)))
(assert (forall ((|#$T0@@39| T@U) (|#$T1@@23| T@U) (|#$T2@@4| T@U) (|#$R@@52| T@U) (bx@@57 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@39|) TyType) (= (type |#$T1@@23|) TyType)) (= (type |#$T2@@4|) TyType)) (= (type |#$R@@52|) TyType)) (= (type bx@@57) BoxType)) ($IsBox bx@@57 (Tclass._System.___hFunc3 |#$T0@@39| |#$T1@@23| |#$T2@@4| |#$R@@52|))) (and (= ($Box ($Unbox HandleTypeType bx@@57)) bx@@57) ($Is ($Unbox HandleTypeType bx@@57) (Tclass._System.___hFunc3 |#$T0@@39| |#$T1@@23| |#$T2@@4| |#$R@@52|))))
 :qid |unknown.0:0|
 :skolemid |779|
 :pattern ( ($IsBox bx@@57 (Tclass._System.___hFunc3 |#$T0@@39| |#$T1@@23| |#$T2@@4| |#$R@@52|)))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (and (forall ((arg0@@165 T@T) (arg1@@75 T@T) (arg2@@33 T@T) (arg3@@13 T@T) (arg4@@4 T@T) ) (! (= (Ctor (MapType4Type arg0@@165 arg1@@75 arg2@@33 arg3@@13 arg4@@4)) 25)
 :qid |ctor:MapType4Type|
)) (forall ((arg0@@166 T@T) (arg1@@76 T@T) (arg2@@34 T@T) (arg3@@14 T@T) (arg4@@5 T@T) ) (! (= (MapType4TypeInv0 (MapType4Type arg0@@166 arg1@@76 arg2@@34 arg3@@14 arg4@@5)) arg0@@166)
 :qid |typeInv:MapType4TypeInv0|
 :pattern ( (MapType4Type arg0@@166 arg1@@76 arg2@@34 arg3@@14 arg4@@5))
))) (forall ((arg0@@167 T@T) (arg1@@77 T@T) (arg2@@35 T@T) (arg3@@15 T@T) (arg4@@6 T@T) ) (! (= (MapType4TypeInv1 (MapType4Type arg0@@167 arg1@@77 arg2@@35 arg3@@15 arg4@@6)) arg1@@77)
 :qid |typeInv:MapType4TypeInv1|
 :pattern ( (MapType4Type arg0@@167 arg1@@77 arg2@@35 arg3@@15 arg4@@6))
))) (forall ((arg0@@168 T@T) (arg1@@78 T@T) (arg2@@36 T@T) (arg3@@16 T@T) (arg4@@7 T@T) ) (! (= (MapType4TypeInv2 (MapType4Type arg0@@168 arg1@@78 arg2@@36 arg3@@16 arg4@@7)) arg2@@36)
 :qid |typeInv:MapType4TypeInv2|
 :pattern ( (MapType4Type arg0@@168 arg1@@78 arg2@@36 arg3@@16 arg4@@7))
))) (forall ((arg0@@169 T@T) (arg1@@79 T@T) (arg2@@37 T@T) (arg3@@17 T@T) (arg4@@8 T@T) ) (! (= (MapType4TypeInv3 (MapType4Type arg0@@169 arg1@@79 arg2@@37 arg3@@17 arg4@@8)) arg3@@17)
 :qid |typeInv:MapType4TypeInv3|
 :pattern ( (MapType4Type arg0@@169 arg1@@79 arg2@@37 arg3@@17 arg4@@8))
))) (forall ((arg0@@170 T@T) (arg1@@80 T@T) (arg2@@38 T@T) (arg3@@18 T@T) (arg4@@9 T@T) ) (! (= (MapType4TypeInv4 (MapType4Type arg0@@170 arg1@@80 arg2@@38 arg3@@18 arg4@@9)) arg4@@9)
 :qid |typeInv:MapType4TypeInv4|
 :pattern ( (MapType4Type arg0@@170 arg1@@80 arg2@@38 arg3@@18 arg4@@9))
))) (forall ((arg0@@171 T@U) (arg1@@81 T@U) (arg2@@39 T@U) (arg3@@19 T@U) (arg4@@10 T@U) ) (! (let ((aVar4 (MapType4TypeInv4 (type arg0@@171))))
(= (type (MapType4Select arg0@@171 arg1@@81 arg2@@39 arg3@@19 arg4@@10)) aVar4))
 :qid |funType:MapType4Select|
 :pattern ( (MapType4Select arg0@@171 arg1@@81 arg2@@39 arg3@@19 arg4@@10))
))) (forall ((arg0@@172 T@U) (arg1@@82 T@U) (arg2@@40 T@U) (arg3@@20 T@U) (arg4@@11 T@U) (arg5@@1 T@U) ) (! (let ((aVar4@@0 (type arg5@@1)))
(let ((aVar3@@2 (type arg4@@11)))
(let ((aVar2@@3 (type arg3@@20)))
(let ((aVar1@@4 (type arg2@@40)))
(let ((aVar0@@2 (type arg1@@82)))
(= (type (MapType4Store arg0@@172 arg1@@82 arg2@@40 arg3@@20 arg4@@11 arg5@@1)) (MapType4Type aVar0@@2 aVar1@@4 aVar2@@3 aVar3@@2 aVar4@@0)))))))
 :qid |funType:MapType4Store|
 :pattern ( (MapType4Store arg0@@172 arg1@@82 arg2@@40 arg3@@20 arg4@@11 arg5@@1))
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
)))) (forall ((arg0@@173 T@U) (arg1@@83 T@U) (arg2@@41 T@U) (arg3@@21 T@U) (arg4@@12 T@U) (arg5@@2 T@U) (arg6@@1 T@U) (arg7 T@U) (arg8 T@U) ) (! (= (type (Apply3 arg0@@173 arg1@@83 arg2@@41 arg3@@21 arg4@@12 arg5@@2 arg6@@1 arg7 arg8)) BoxType)
 :qid |funType:Apply3|
 :pattern ( (Apply3 arg0@@173 arg1@@83 arg2@@41 arg3@@21 arg4@@12 arg5@@2 arg6@@1 arg7 arg8))
))) (forall ((arg0@@174 T@U) (arg1@@84 T@U) (arg2@@42 T@U) ) (! (= (type (Handle3 arg0@@174 arg1@@84 arg2@@42)) HandleTypeType)
 :qid |funType:Handle3|
 :pattern ( (Handle3 arg0@@174 arg1@@84 arg2@@42))
))))
(assert (forall ((t0@@57 T@U) (t1@@33 T@U) (t2@@14 T@U) (t3 T@U) (heap@@16 T@U) (h@@41 T@U) (r@@21 T@U) (rd@@8 T@U) (bx0@@31 T@U) (bx1@@15 T@U) (bx2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@57) TyType) (= (type t1@@33) TyType)) (= (type t2@@14) TyType)) (= (type t3) TyType)) (= (type heap@@16) (MapType0Type refType MapType1Type))) (= (type h@@41) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType))) (= (type r@@21) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType boolType))) (= (type rd@@8) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@31) BoxType)) (= (type bx1@@15) BoxType)) (= (type bx2) BoxType)) (= (Apply3 t0@@57 t1@@33 t2@@14 t3 heap@@16 (Handle3 h@@41 r@@21 rd@@8) bx0@@31 bx1@@15 bx2) (MapType4Select h@@41 heap@@16 bx0@@31 bx1@@15 bx2)))
 :qid |unknown.0:0|
 :skolemid |780|
 :pattern ( (Apply3 t0@@57 t1@@33 t2@@14 t3 heap@@16 (Handle3 h@@41 r@@21 rd@@8) bx0@@31 bx1@@15 bx2))
)))
(assert (forall ((t0@@58 T@U) (t1@@34 T@U) (t2@@15 T@U) (t3@@0 T@U) (heap@@17 T@U) (h@@42 T@U) (r@@22 T@U) (rd@@9 T@U) (bx0@@32 T@U) (bx1@@16 T@U) (bx2@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@58) TyType) (= (type t1@@34) TyType)) (= (type t2@@15) TyType)) (= (type t3@@0) TyType)) (= (type heap@@17) (MapType0Type refType MapType1Type))) (= (type h@@42) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType))) (= (type r@@22) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType boolType))) (= (type rd@@9) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@32) BoxType)) (= (type bx1@@16) BoxType)) (= (type bx2@@0) BoxType)) (U_2_bool (MapType4Select r@@22 heap@@17 bx0@@32 bx1@@16 bx2@@0))) (Requires3 t0@@58 t1@@34 t2@@15 t3@@0 heap@@17 (Handle3 h@@42 r@@22 rd@@9) bx0@@32 bx1@@16 bx2@@0))
 :qid |unknown.0:0|
 :skolemid |781|
 :pattern ( (Requires3 t0@@58 t1@@34 t2@@15 t3@@0 heap@@17 (Handle3 h@@42 r@@22 rd@@9) bx0@@32 bx1@@16 bx2@@0))
)))
(assert (forall ((arg0@@175 T@U) (arg1@@85 T@U) (arg2@@43 T@U) (arg3@@22 T@U) (arg4@@13 T@U) (arg5@@3 T@U) (arg6@@2 T@U) (arg7@@0 T@U) (arg8@@0 T@U) ) (! (= (type (Reads3 arg0@@175 arg1@@85 arg2@@43 arg3@@22 arg4@@13 arg5@@3 arg6@@2 arg7@@0 arg8@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads3|
 :pattern ( (Reads3 arg0@@175 arg1@@85 arg2@@43 arg3@@22 arg4@@13 arg5@@3 arg6@@2 arg7@@0 arg8@@0))
)))
(assert (forall ((t0@@59 T@U) (t1@@35 T@U) (t2@@16 T@U) (t3@@1 T@U) (heap@@18 T@U) (h@@43 T@U) (r@@23 T@U) (rd@@10 T@U) (bx0@@33 T@U) (bx1@@17 T@U) (bx2@@1 T@U) (bx@@58 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@59) TyType) (= (type t1@@35) TyType)) (= (type t2@@16) TyType)) (= (type t3@@1) TyType)) (= (type heap@@18) (MapType0Type refType MapType1Type))) (= (type h@@43) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType))) (= (type r@@23) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType boolType))) (= (type rd@@10) (MapType4Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@33) BoxType)) (= (type bx1@@17) BoxType)) (= (type bx2@@1) BoxType)) (= (type bx@@58) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads3 t0@@59 t1@@35 t2@@16 t3@@1 heap@@18 (Handle3 h@@43 r@@23 rd@@10) bx0@@33 bx1@@17 bx2@@1) bx@@58)) (U_2_bool (MapType0Select (MapType4Select rd@@10 heap@@18 bx0@@33 bx1@@17 bx2@@1) bx@@58))) (=> (U_2_bool (MapType0Select (MapType4Select rd@@10 heap@@18 bx0@@33 bx1@@17 bx2@@1) bx@@58)) (U_2_bool (MapType0Select (Reads3 t0@@59 t1@@35 t2@@16 t3@@1 heap@@18 (Handle3 h@@43 r@@23 rd@@10) bx0@@33 bx1@@17 bx2@@1) bx@@58)))))
 :qid |unknown.0:0|
 :skolemid |782|
 :pattern ( (MapType0Select (Reads3 t0@@59 t1@@35 t2@@16 t3@@1 heap@@18 (Handle3 h@@43 r@@23 rd@@10) bx0@@33 bx1@@17 bx2@@1) bx@@58))
)))
(assert (forall ((t0@@60 T@U) (t1@@36 T@U) (t2@@17 T@U) (t3@@2 T@U) (h0@@18 T@U) (h1@@18 T@U) (f@@41 T@U) (bx0@@34 T@U) (bx1@@18 T@U) (bx2@@2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@60) TyType) (= (type t1@@36) TyType)) (= (type t2@@17) TyType)) (= (type t3@@2) TyType)) (= (type h0@@18) (MapType0Type refType MapType1Type))) (= (type h1@@18) (MapType0Type refType MapType1Type))) (= (type f@@41) HandleTypeType)) (= (type bx0@@34) BoxType)) (= (type bx1@@18) BoxType)) (= (type bx2@@2) BoxType)) (and (and (and ($HeapSucc h0@@18 h1@@18) (and ($IsGoodHeap h0@@18) ($IsGoodHeap h1@@18))) (and (and (and ($IsBox bx0@@34 t0@@60) ($IsBox bx1@@18 t1@@36)) ($IsBox bx2@@2 t2@@17)) ($Is f@@41 (Tclass._System.___hFunc3 t0@@60 t1@@36 t2@@17 t3@@2)))) (forall ((o@@72 T@U) (fld@@17 T@U) ) (! (let ((a@@97 (FieldTypeInv0 (type fld@@17))))
 (=> (and (and (= (type o@@72) refType) (= (type fld@@17) (FieldType a@@97))) (and (not (= o@@72 null)) (U_2_bool (MapType0Select (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h0@@18 f@@41 bx0@@34 bx1@@18 bx2@@2) ($Box o@@72))))) (= (MapType1Select (MapType0Select h0@@18 o@@72) fld@@17) (MapType1Select (MapType0Select h1@@18 o@@72) fld@@17))))
 :qid |unknown.0:0|
 :skolemid |783|
 :no-pattern (type o@@72)
 :no-pattern (type fld@@17)
 :no-pattern (U_2_int o@@72)
 :no-pattern (U_2_bool o@@72)
 :no-pattern (U_2_int fld@@17)
 :no-pattern (U_2_bool fld@@17)
)))) (= (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h0@@18 f@@41 bx0@@34 bx1@@18 bx2@@2) (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h1@@18 f@@41 bx0@@34 bx1@@18 bx2@@2)))
 :qid |unknown.0:0|
 :skolemid |784|
 :pattern ( ($HeapSucc h0@@18 h1@@18) (Reads3 t0@@60 t1@@36 t2@@17 t3@@2 h1@@18 f@@41 bx0@@34 bx1@@18 bx2@@2))
)))
(assert (forall ((t0@@61 T@U) (t1@@37 T@U) (t2@@18 T@U) (t3@@3 T@U) (h0@@19 T@U) (h1@@19 T@U) (f@@42 T@U) (bx0@@35 T@U) (bx1@@19 T@U) (bx2@@3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@61) TyType) (= (type t1@@37) TyType)) (= (type t2@@18) TyType)) (= (type t3@@3) TyType)) (= (type h0@@19) (MapType0Type refType MapType1Type))) (= (type h1@@19) (MapType0Type refType MapType1Type))) (= (type f@@42) HandleTypeType)) (= (type bx0@@35) BoxType)) (= (type bx1@@19) BoxType)) (= (type bx2@@3) BoxType)) (and (and (and ($HeapSucc h0@@19 h1@@19) (and ($IsGoodHeap h0@@19) ($IsGoodHeap h1@@19))) (and (and (and ($IsBox bx0@@35 t0@@61) ($IsBox bx1@@19 t1@@37)) ($IsBox bx2@@3 t2@@18)) ($Is f@@42 (Tclass._System.___hFunc3 t0@@61 t1@@37 t2@@18 t3@@3)))) (forall ((o@@73 T@U) (fld@@18 T@U) ) (! (let ((a@@98 (FieldTypeInv0 (type fld@@18))))
 (=> (and (and (= (type o@@73) refType) (= (type fld@@18) (FieldType a@@98))) (and (not (= o@@73 null)) (U_2_bool (MapType0Select (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h1@@19 f@@42 bx0@@35 bx1@@19 bx2@@3) ($Box o@@73))))) (= (MapType1Select (MapType0Select h0@@19 o@@73) fld@@18) (MapType1Select (MapType0Select h1@@19 o@@73) fld@@18))))
 :qid |unknown.0:0|
 :skolemid |785|
 :no-pattern (type o@@73)
 :no-pattern (type fld@@18)
 :no-pattern (U_2_int o@@73)
 :no-pattern (U_2_bool o@@73)
 :no-pattern (U_2_int fld@@18)
 :no-pattern (U_2_bool fld@@18)
)))) (= (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h0@@19 f@@42 bx0@@35 bx1@@19 bx2@@3) (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h1@@19 f@@42 bx0@@35 bx1@@19 bx2@@3)))
 :qid |unknown.0:0|
 :skolemid |786|
 :pattern ( ($HeapSucc h0@@19 h1@@19) (Reads3 t0@@61 t1@@37 t2@@18 t3@@3 h1@@19 f@@42 bx0@@35 bx1@@19 bx2@@3))
)))
(assert (forall ((t0@@62 T@U) (t1@@38 T@U) (t2@@19 T@U) (t3@@4 T@U) (h0@@20 T@U) (h1@@20 T@U) (f@@43 T@U) (bx0@@36 T@U) (bx1@@20 T@U) (bx2@@4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@62) TyType) (= (type t1@@38) TyType)) (= (type t2@@19) TyType)) (= (type t3@@4) TyType)) (= (type h0@@20) (MapType0Type refType MapType1Type))) (= (type h1@@20) (MapType0Type refType MapType1Type))) (= (type f@@43) HandleTypeType)) (= (type bx0@@36) BoxType)) (= (type bx1@@20) BoxType)) (= (type bx2@@4) BoxType)) (and (and (and ($HeapSucc h0@@20 h1@@20) (and ($IsGoodHeap h0@@20) ($IsGoodHeap h1@@20))) (and (and (and ($IsBox bx0@@36 t0@@62) ($IsBox bx1@@20 t1@@38)) ($IsBox bx2@@4 t2@@19)) ($Is f@@43 (Tclass._System.___hFunc3 t0@@62 t1@@38 t2@@19 t3@@4)))) (forall ((o@@74 T@U) (fld@@19 T@U) ) (! (let ((a@@99 (FieldTypeInv0 (type fld@@19))))
 (=> (and (and (= (type o@@74) refType) (= (type fld@@19) (FieldType a@@99))) (and (not (= o@@74 null)) (U_2_bool (MapType0Select (Reads3 t0@@62 t1@@38 t2@@19 t3@@4 h0@@20 f@@43 bx0@@36 bx1@@20 bx2@@4) ($Box o@@74))))) (= (MapType1Select (MapType0Select h0@@20 o@@74) fld@@19) (MapType1Select (MapType0Select h1@@20 o@@74) fld@@19))))
 :qid |unknown.0:0|
 :skolemid |787|
 :no-pattern (type o@@74)
 :no-pattern (type fld@@19)
 :no-pattern (U_2_int o@@74)
 :no-pattern (U_2_bool o@@74)
 :no-pattern (U_2_int fld@@19)
 :no-pattern (U_2_bool fld@@19)
)))) (and (=> (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h0@@20 f@@43 bx0@@36 bx1@@20 bx2@@4) (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h1@@20 f@@43 bx0@@36 bx1@@20 bx2@@4)) (=> (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h1@@20 f@@43 bx0@@36 bx1@@20 bx2@@4) (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h0@@20 f@@43 bx0@@36 bx1@@20 bx2@@4))))
 :qid |unknown.0:0|
 :skolemid |788|
 :pattern ( ($HeapSucc h0@@20 h1@@20) (Requires3 t0@@62 t1@@38 t2@@19 t3@@4 h1@@20 f@@43 bx0@@36 bx1@@20 bx2@@4))
)))
(assert (forall ((t0@@63 T@U) (t1@@39 T@U) (t2@@20 T@U) (t3@@5 T@U) (h0@@21 T@U) (h1@@21 T@U) (f@@44 T@U) (bx0@@37 T@U) (bx1@@21 T@U) (bx2@@5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@63) TyType) (= (type t1@@39) TyType)) (= (type t2@@20) TyType)) (= (type t3@@5) TyType)) (= (type h0@@21) (MapType0Type refType MapType1Type))) (= (type h1@@21) (MapType0Type refType MapType1Type))) (= (type f@@44) HandleTypeType)) (= (type bx0@@37) BoxType)) (= (type bx1@@21) BoxType)) (= (type bx2@@5) BoxType)) (and (and (and ($HeapSucc h0@@21 h1@@21) (and ($IsGoodHeap h0@@21) ($IsGoodHeap h1@@21))) (and (and (and ($IsBox bx0@@37 t0@@63) ($IsBox bx1@@21 t1@@39)) ($IsBox bx2@@5 t2@@20)) ($Is f@@44 (Tclass._System.___hFunc3 t0@@63 t1@@39 t2@@20 t3@@5)))) (forall ((o@@75 T@U) (fld@@20 T@U) ) (! (let ((a@@100 (FieldTypeInv0 (type fld@@20))))
 (=> (and (and (= (type o@@75) refType) (= (type fld@@20) (FieldType a@@100))) (and (not (= o@@75 null)) (U_2_bool (MapType0Select (Reads3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5) ($Box o@@75))))) (= (MapType1Select (MapType0Select h0@@21 o@@75) fld@@20) (MapType1Select (MapType0Select h1@@21 o@@75) fld@@20))))
 :qid |unknown.0:0|
 :skolemid |789|
 :no-pattern (type o@@75)
 :no-pattern (type fld@@20)
 :no-pattern (U_2_int o@@75)
 :no-pattern (U_2_bool o@@75)
 :no-pattern (U_2_int fld@@20)
 :no-pattern (U_2_bool fld@@20)
)))) (and (=> (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h0@@21 f@@44 bx0@@37 bx1@@21 bx2@@5) (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5)) (=> (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5) (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h0@@21 f@@44 bx0@@37 bx1@@21 bx2@@5))))
 :qid |unknown.0:0|
 :skolemid |790|
 :pattern ( ($HeapSucc h0@@21 h1@@21) (Requires3 t0@@63 t1@@39 t2@@20 t3@@5 h1@@21 f@@44 bx0@@37 bx1@@21 bx2@@5))
)))
(assert (forall ((t0@@64 T@U) (t1@@40 T@U) (t2@@21 T@U) (t3@@6 T@U) (h0@@22 T@U) (h1@@22 T@U) (f@@45 T@U) (bx0@@38 T@U) (bx1@@22 T@U) (bx2@@6 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@64) TyType) (= (type t1@@40) TyType)) (= (type t2@@21) TyType)) (= (type t3@@6) TyType)) (= (type h0@@22) (MapType0Type refType MapType1Type))) (= (type h1@@22) (MapType0Type refType MapType1Type))) (= (type f@@45) HandleTypeType)) (= (type bx0@@38) BoxType)) (= (type bx1@@22) BoxType)) (= (type bx2@@6) BoxType)) (and (and (and ($HeapSucc h0@@22 h1@@22) (and ($IsGoodHeap h0@@22) ($IsGoodHeap h1@@22))) (and (and (and ($IsBox bx0@@38 t0@@64) ($IsBox bx1@@22 t1@@40)) ($IsBox bx2@@6 t2@@21)) ($Is f@@45 (Tclass._System.___hFunc3 t0@@64 t1@@40 t2@@21 t3@@6)))) (forall ((o@@76 T@U) (fld@@21 T@U) ) (! (let ((a@@101 (FieldTypeInv0 (type fld@@21))))
 (=> (and (and (= (type o@@76) refType) (= (type fld@@21) (FieldType a@@101))) (and (not (= o@@76 null)) (U_2_bool (MapType0Select (Reads3 t0@@64 t1@@40 t2@@21 t3@@6 h0@@22 f@@45 bx0@@38 bx1@@22 bx2@@6) ($Box o@@76))))) (= (MapType1Select (MapType0Select h0@@22 o@@76) fld@@21) (MapType1Select (MapType0Select h1@@22 o@@76) fld@@21))))
 :qid |unknown.0:0|
 :skolemid |791|
 :no-pattern (type o@@76)
 :no-pattern (type fld@@21)
 :no-pattern (U_2_int o@@76)
 :no-pattern (U_2_bool o@@76)
 :no-pattern (U_2_int fld@@21)
 :no-pattern (U_2_bool fld@@21)
)))) (= (Apply3 t0@@64 t1@@40 t2@@21 t3@@6 h0@@22 f@@45 bx0@@38 bx1@@22 bx2@@6) (Apply3 t0@@64 t1@@40 t2@@21 t3@@6 h1@@22 f@@45 bx0@@38 bx1@@22 bx2@@6)))
 :qid |unknown.0:0|
 :skolemid |792|
 :pattern ( ($HeapSucc h0@@22 h1@@22) (Apply3 t0@@64 t1@@40 t2@@21 t3@@6 h1@@22 f@@45 bx0@@38 bx1@@22 bx2@@6))
)))
(assert (forall ((t0@@65 T@U) (t1@@41 T@U) (t2@@22 T@U) (t3@@7 T@U) (h0@@23 T@U) (h1@@23 T@U) (f@@46 T@U) (bx0@@39 T@U) (bx1@@23 T@U) (bx2@@7 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (= (type t0@@65) TyType) (= (type t1@@41) TyType)) (= (type t2@@22) TyType)) (= (type t3@@7) TyType)) (= (type h0@@23) (MapType0Type refType MapType1Type))) (= (type h1@@23) (MapType0Type refType MapType1Type))) (= (type f@@46) HandleTypeType)) (= (type bx0@@39) BoxType)) (= (type bx1@@23) BoxType)) (= (type bx2@@7) BoxType)) (and (and (and ($HeapSucc h0@@23 h1@@23) (and ($IsGoodHeap h0@@23) ($IsGoodHeap h1@@23))) (and (and (and ($IsBox bx0@@39 t0@@65) ($IsBox bx1@@23 t1@@41)) ($IsBox bx2@@7 t2@@22)) ($Is f@@46 (Tclass._System.___hFunc3 t0@@65 t1@@41 t2@@22 t3@@7)))) (forall ((o@@77 T@U) (fld@@22 T@U) ) (! (let ((a@@102 (FieldTypeInv0 (type fld@@22))))
 (=> (and (and (= (type o@@77) refType) (= (type fld@@22) (FieldType a@@102))) (and (not (= o@@77 null)) (U_2_bool (MapType0Select (Reads3 t0@@65 t1@@41 t2@@22 t3@@7 h1@@23 f@@46 bx0@@39 bx1@@23 bx2@@7) ($Box o@@77))))) (= (MapType1Select (MapType0Select h0@@23 o@@77) fld@@22) (MapType1Select (MapType0Select h1@@23 o@@77) fld@@22))))
 :qid |unknown.0:0|
 :skolemid |793|
 :no-pattern (type o@@77)
 :no-pattern (type fld@@22)
 :no-pattern (U_2_int o@@77)
 :no-pattern (U_2_bool o@@77)
 :no-pattern (U_2_int fld@@22)
 :no-pattern (U_2_bool fld@@22)
)))) (= (Apply3 t0@@65 t1@@41 t2@@22 t3@@7 h0@@23 f@@46 bx0@@39 bx1@@23 bx2@@7) (Apply3 t0@@65 t1@@41 t2@@22 t3@@7 h1@@23 f@@46 bx0@@39 bx1@@23 bx2@@7)))
 :qid |unknown.0:0|
 :skolemid |794|
 :pattern ( ($HeapSucc h0@@23 h1@@23) (Apply3 t0@@65 t1@@41 t2@@22 t3@@7 h1@@23 f@@46 bx0@@39 bx1@@23 bx2@@7))
)))
(assert (forall ((t0@@66 T@U) (t1@@42 T@U) (t2@@23 T@U) (t3@@8 T@U) (heap@@19 T@U) (f@@47 T@U) (bx0@@40 T@U) (bx1@@24 T@U) (bx2@@8 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@66) TyType) (= (type t1@@42) TyType)) (= (type t2@@23) TyType)) (= (type t3@@8) TyType)) (= (type heap@@19) (MapType0Type refType MapType1Type))) (= (type f@@47) HandleTypeType)) (= (type bx0@@40) BoxType)) (= (type bx1@@24) BoxType)) (= (type bx2@@8) BoxType)) (and ($IsGoodHeap heap@@19) (and (and (and ($IsBox bx0@@40 t0@@66) ($IsBox bx1@@24 t1@@42)) ($IsBox bx2@@8 t2@@23)) ($Is f@@47 (Tclass._System.___hFunc3 t0@@66 t1@@42 t2@@23 t3@@8))))) (and (=> (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 $OneHeap f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 heap@@19 f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 heap@@19 f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 $OneHeap f@@47 bx0@@40 bx1@@24 bx2@@8) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |795|
 :pattern ( (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 $OneHeap f@@47 bx0@@40 bx1@@24 bx2@@8) ($IsGoodHeap heap@@19))
 :pattern ( (Reads3 t0@@66 t1@@42 t2@@23 t3@@8 heap@@19 f@@47 bx0@@40 bx1@@24 bx2@@8))
)))
(assert (forall ((t0@@67 T@U) (t1@@43 T@U) (t2@@24 T@U) (t3@@9 T@U) (heap@@20 T@U) (f@@48 T@U) (bx0@@41 T@U) (bx1@@25 T@U) (bx2@@9 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@67) TyType) (= (type t1@@43) TyType)) (= (type t2@@24) TyType)) (= (type t3@@9) TyType)) (= (type heap@@20) (MapType0Type refType MapType1Type))) (= (type f@@48) HandleTypeType)) (= (type bx0@@41) BoxType)) (= (type bx1@@25) BoxType)) (= (type bx2@@9) BoxType)) (and (and ($IsGoodHeap heap@@20) (and (and (and ($IsBox bx0@@41 t0@@67) ($IsBox bx1@@25 t1@@43)) ($IsBox bx2@@9 t2@@24)) ($Is f@@48 (Tclass._System.___hFunc3 t0@@67 t1@@43 t2@@24 t3@@9)))) (|Set#Equal| (Reads3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9) (|Set#Empty| BoxType)))) (and (=> (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9) (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 heap@@20 f@@48 bx0@@41 bx1@@25 bx2@@9)) (=> (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 heap@@20 f@@48 bx0@@41 bx1@@25 bx2@@9) (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9))))
 :qid |unknown.0:0|
 :skolemid |796|
 :pattern ( (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 $OneHeap f@@48 bx0@@41 bx1@@25 bx2@@9) ($IsGoodHeap heap@@20))
 :pattern ( (Requires3 t0@@67 t1@@43 t2@@24 t3@@9 heap@@20 f@@48 bx0@@41 bx1@@25 bx2@@9))
)))
(assert (forall ((f@@49 T@U) (t0@@68 T@U) (t1@@44 T@U) (t2@@25 T@U) (t3@@10 T@U) ) (!  (=> (and (and (and (and (= (type f@@49) HandleTypeType) (= (type t0@@68) TyType)) (= (type t1@@44) TyType)) (= (type t2@@25) TyType)) (= (type t3@@10) TyType)) (and (=> ($Is f@@49 (Tclass._System.___hFunc3 t0@@68 t1@@44 t2@@25 t3@@10)) (forall ((h@@44 T@U) (bx0@@42 T@U) (bx1@@26 T@U) (bx2@@10 T@U) ) (!  (=> (and (and (and (and (= (type h@@44) (MapType0Type refType MapType1Type)) (= (type bx0@@42) BoxType)) (= (type bx1@@26) BoxType)) (= (type bx2@@10) BoxType)) (and (and ($IsGoodHeap h@@44) (and (and ($IsBox bx0@@42 t0@@68) ($IsBox bx1@@26 t1@@44)) ($IsBox bx2@@10 t2@@25))) (Requires3 t0@@68 t1@@44 t2@@25 t3@@10 h@@44 f@@49 bx0@@42 bx1@@26 bx2@@10))) ($IsBox (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@44 f@@49 bx0@@42 bx1@@26 bx2@@10) t3@@10))
 :qid |DafnyPre.515:12|
 :skolemid |797|
 :pattern ( (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@44 f@@49 bx0@@42 bx1@@26 bx2@@10))
))) (=> (forall ((h@@45 T@U) (bx0@@43 T@U) (bx1@@27 T@U) (bx2@@11 T@U) ) (!  (=> (and (and (and (and (= (type h@@45) (MapType0Type refType MapType1Type)) (= (type bx0@@43) BoxType)) (= (type bx1@@27) BoxType)) (= (type bx2@@11) BoxType)) (and (and ($IsGoodHeap h@@45) (and (and ($IsBox bx0@@43 t0@@68) ($IsBox bx1@@27 t1@@44)) ($IsBox bx2@@11 t2@@25))) (Requires3 t0@@68 t1@@44 t2@@25 t3@@10 h@@45 f@@49 bx0@@43 bx1@@27 bx2@@11))) ($IsBox (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@45 f@@49 bx0@@43 bx1@@27 bx2@@11) t3@@10))
 :qid |DafnyPre.515:12|
 :skolemid |797|
 :pattern ( (Apply3 t0@@68 t1@@44 t2@@25 t3@@10 h@@45 f@@49 bx0@@43 bx1@@27 bx2@@11))
)) ($Is f@@49 (Tclass._System.___hFunc3 t0@@68 t1@@44 t2@@25 t3@@10)))))
 :qid |unknown.0:0|
 :skolemid |798|
 :pattern ( ($Is f@@49 (Tclass._System.___hFunc3 t0@@68 t1@@44 t2@@25 t3@@10)))
)))
(assert (forall ((f@@50 T@U) (t0@@69 T@U) (t1@@45 T@U) (t2@@26 T@U) (t3@@11 T@U) (u0@@2 T@U) (u1@@1 T@U) (u2@@0 T@U) (u3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type f@@50) HandleTypeType) (= (type t0@@69) TyType)) (= (type t1@@45) TyType)) (= (type t2@@26) TyType)) (= (type t3@@11) TyType)) (= (type u0@@2) TyType)) (= (type u1@@1) TyType)) (= (type u2@@0) TyType)) (= (type u3) TyType)) (and (and (and (and ($Is f@@50 (Tclass._System.___hFunc3 t0@@69 t1@@45 t2@@26 t3@@11)) (forall ((bx@@59 T@U) ) (!  (=> (and (= (type bx@@59) BoxType) ($IsBox bx@@59 u0@@2)) ($IsBox bx@@59 t0@@69))
 :qid |unknown.0:0|
 :skolemid |799|
 :pattern ( ($IsBox bx@@59 u0@@2))
 :pattern ( ($IsBox bx@@59 t0@@69))
))) (forall ((bx@@60 T@U) ) (!  (=> (and (= (type bx@@60) BoxType) ($IsBox bx@@60 u1@@1)) ($IsBox bx@@60 t1@@45))
 :qid |unknown.0:0|
 :skolemid |800|
 :pattern ( ($IsBox bx@@60 u1@@1))
 :pattern ( ($IsBox bx@@60 t1@@45))
))) (forall ((bx@@61 T@U) ) (!  (=> (and (= (type bx@@61) BoxType) ($IsBox bx@@61 u2@@0)) ($IsBox bx@@61 t2@@26))
 :qid |unknown.0:0|
 :skolemid |801|
 :pattern ( ($IsBox bx@@61 u2@@0))
 :pattern ( ($IsBox bx@@61 t2@@26))
))) (forall ((bx@@62 T@U) ) (!  (=> (and (= (type bx@@62) BoxType) ($IsBox bx@@62 t3@@11)) ($IsBox bx@@62 u3))
 :qid |unknown.0:0|
 :skolemid |802|
 :pattern ( ($IsBox bx@@62 t3@@11))
 :pattern ( ($IsBox bx@@62 u3))
)))) ($Is f@@50 (Tclass._System.___hFunc3 u0@@2 u1@@1 u2@@0 u3)))
 :qid |unknown.0:0|
 :skolemid |803|
 :pattern ( ($Is f@@50 (Tclass._System.___hFunc3 t0@@69 t1@@45 t2@@26 t3@@11)) ($Is f@@50 (Tclass._System.___hFunc3 u0@@2 u1@@1 u2@@0 u3)))
)))
(assert (forall ((f@@51 T@U) (t0@@70 T@U) (t1@@46 T@U) (t2@@27 T@U) (t3@@12 T@U) (h@@46 T@U) ) (!  (=> (and (and (and (and (and (and (= (type f@@51) HandleTypeType) (= (type t0@@70) TyType)) (= (type t1@@46) TyType)) (= (type t2@@27) TyType)) (= (type t3@@12) TyType)) (= (type h@@46) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@46)) (and (=> ($IsAlloc f@@51 (Tclass._System.___hFunc3 t0@@70 t1@@46 t2@@27 t3@@12) h@@46) (forall ((bx0@@44 T@U) (bx1@@28 T@U) (bx2@@12 T@U) ) (!  (=> (and (and (= (type bx0@@44) BoxType) (= (type bx1@@28) BoxType)) (= (type bx2@@12) BoxType)) (=> (and (and (and (and ($IsBox bx0@@44 t0@@70) ($IsAllocBox bx0@@44 t0@@70 h@@46)) (and ($IsBox bx1@@28 t1@@46) ($IsAllocBox bx1@@28 t1@@46 h@@46))) (and ($IsBox bx2@@12 t2@@27) ($IsAllocBox bx2@@12 t2@@27 h@@46))) (Requires3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12)) (forall ((r@@24 T@U) ) (!  (=> (= (type r@@24) refType) (=> (and (not (= r@@24 null)) (U_2_bool (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12) ($Box r@@24)))) (U_2_bool (MapType1Select (MapType0Select h@@46 r@@24) alloc))))
 :qid |unknown.0:0|
 :skolemid |804|
 :pattern ( (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12) ($Box r@@24)))
))))
 :qid |unknown.0:0|
 :skolemid |805|
 :pattern ( (Apply3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12))
 :pattern ( (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@44 bx1@@28 bx2@@12))
))) (=> (forall ((bx0@@45 T@U) (bx1@@29 T@U) (bx2@@13 T@U) ) (!  (=> (and (and (= (type bx0@@45) BoxType) (= (type bx1@@29) BoxType)) (= (type bx2@@13) BoxType)) (=> (and (and (and (and ($IsBox bx0@@45 t0@@70) ($IsAllocBox bx0@@45 t0@@70 h@@46)) (and ($IsBox bx1@@29 t1@@46) ($IsAllocBox bx1@@29 t1@@46 h@@46))) (and ($IsBox bx2@@13 t2@@27) ($IsAllocBox bx2@@13 t2@@27 h@@46))) (Requires3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13)) (forall ((r@@25 T@U) ) (!  (=> (= (type r@@25) refType) (=> (and (not (= r@@25 null)) (U_2_bool (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13) ($Box r@@25)))) (U_2_bool (MapType1Select (MapType0Select h@@46 r@@25) alloc))))
 :qid |unknown.0:0|
 :skolemid |804|
 :pattern ( (MapType0Select (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13) ($Box r@@25)))
))))
 :qid |unknown.0:0|
 :skolemid |805|
 :pattern ( (Apply3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13))
 :pattern ( (Reads3 t0@@70 t1@@46 t2@@27 t3@@12 h@@46 f@@51 bx0@@45 bx1@@29 bx2@@13))
)) ($IsAlloc f@@51 (Tclass._System.___hFunc3 t0@@70 t1@@46 t2@@27 t3@@12) h@@46))))
 :qid |unknown.0:0|
 :skolemid |806|
 :pattern ( ($IsAlloc f@@51 (Tclass._System.___hFunc3 t0@@70 t1@@46 t2@@27 t3@@12) h@@46))
)))
(assert (forall ((f@@52 T@U) (t0@@71 T@U) (t1@@47 T@U) (t2@@28 T@U) (t3@@13 T@U) (h@@47 T@U) ) (!  (=> (and (and (and (and (and (and (= (type f@@52) HandleTypeType) (= (type t0@@71) TyType)) (= (type t1@@47) TyType)) (= (type t2@@28) TyType)) (= (type t3@@13) TyType)) (= (type h@@47) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@47) ($IsAlloc f@@52 (Tclass._System.___hFunc3 t0@@71 t1@@47 t2@@28 t3@@13) h@@47))) (forall ((bx0@@46 T@U) (bx1@@30 T@U) (bx2@@14 T@U) ) (!  (=> (and (and (= (type bx0@@46) BoxType) (= (type bx1@@30) BoxType)) (= (type bx2@@14) BoxType)) (=> (and (and (and ($IsAllocBox bx0@@46 t0@@71 h@@47) ($IsAllocBox bx1@@30 t1@@47 h@@47)) ($IsAllocBox bx2@@14 t2@@28 h@@47)) (Requires3 t0@@71 t1@@47 t2@@28 t3@@13 h@@47 f@@52 bx0@@46 bx1@@30 bx2@@14)) ($IsAllocBox (Apply3 t0@@71 t1@@47 t2@@28 t3@@13 h@@47 f@@52 bx0@@46 bx1@@30 bx2@@14) t3@@13 h@@47)))
 :qid |unknown.0:0|
 :skolemid |807|
 :pattern ( (Apply3 t0@@71 t1@@47 t2@@28 t3@@13 h@@47 f@@52 bx0@@46 bx1@@30 bx2@@14))
)))
 :qid |unknown.0:0|
 :skolemid |808|
 :pattern ( ($IsAlloc f@@52 (Tclass._System.___hFunc3 t0@@71 t1@@47 t2@@28 t3@@13) h@@47))
)))
(assert (forall ((arg0@@176 T@U) (arg1@@86 T@U) (arg2@@44 T@U) (arg3@@23 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3 arg0@@176 arg1@@86 arg2@@44 arg3@@23)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3|
 :pattern ( (Tclass._System.___hPartialFunc3 arg0@@176 arg1@@86 arg2@@44 arg3@@23))
)))
(assert (forall ((|#$T0@@40| T@U) (|#$T1@@24| T@U) (|#$T2@@5| T@U) (|#$R@@53| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@40|) TyType) (= (type |#$T1@@24|) TyType)) (= (type |#$T2@@5|) TyType)) (= (type |#$R@@53|) TyType)) (= (Tag (Tclass._System.___hPartialFunc3 |#$T0@@40| |#$T1@@24| |#$T2@@5| |#$R@@53|)) Tagclass._System.___hPartialFunc3))
 :qid |unknown.0:0|
 :skolemid |809|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@40| |#$T1@@24| |#$T2@@5| |#$R@@53|))
)))
(assert (forall ((arg0@@177 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_0 arg0@@177)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_0|
 :pattern ( (Tclass._System.___hPartialFunc3_0 arg0@@177))
)))
(assert (forall ((|#$T0@@41| T@U) (|#$T1@@25| T@U) (|#$T2@@6| T@U) (|#$R@@54| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@41|) TyType) (= (type |#$T1@@25|) TyType)) (= (type |#$T2@@6|) TyType)) (= (type |#$R@@54|) TyType)) (= (Tclass._System.___hPartialFunc3_0 (Tclass._System.___hPartialFunc3 |#$T0@@41| |#$T1@@25| |#$T2@@6| |#$R@@54|)) |#$T0@@41|))
 :qid |unknown.0:0|
 :skolemid |810|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@41| |#$T1@@25| |#$T2@@6| |#$R@@54|))
)))
(assert (forall ((arg0@@178 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_1 arg0@@178)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_1|
 :pattern ( (Tclass._System.___hPartialFunc3_1 arg0@@178))
)))
(assert (forall ((|#$T0@@42| T@U) (|#$T1@@26| T@U) (|#$T2@@7| T@U) (|#$R@@55| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@42|) TyType) (= (type |#$T1@@26|) TyType)) (= (type |#$T2@@7|) TyType)) (= (type |#$R@@55|) TyType)) (= (Tclass._System.___hPartialFunc3_1 (Tclass._System.___hPartialFunc3 |#$T0@@42| |#$T1@@26| |#$T2@@7| |#$R@@55|)) |#$T1@@26|))
 :qid |unknown.0:0|
 :skolemid |811|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@42| |#$T1@@26| |#$T2@@7| |#$R@@55|))
)))
(assert (forall ((arg0@@179 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_2 arg0@@179)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_2|
 :pattern ( (Tclass._System.___hPartialFunc3_2 arg0@@179))
)))
(assert (forall ((|#$T0@@43| T@U) (|#$T1@@27| T@U) (|#$T2@@8| T@U) (|#$R@@56| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@43|) TyType) (= (type |#$T1@@27|) TyType)) (= (type |#$T2@@8|) TyType)) (= (type |#$R@@56|) TyType)) (= (Tclass._System.___hPartialFunc3_2 (Tclass._System.___hPartialFunc3 |#$T0@@43| |#$T1@@27| |#$T2@@8| |#$R@@56|)) |#$T2@@8|))
 :qid |unknown.0:0|
 :skolemid |812|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@43| |#$T1@@27| |#$T2@@8| |#$R@@56|))
)))
(assert (forall ((arg0@@180 T@U) ) (! (= (type (Tclass._System.___hPartialFunc3_3 arg0@@180)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc3_3|
 :pattern ( (Tclass._System.___hPartialFunc3_3 arg0@@180))
)))
(assert (forall ((|#$T0@@44| T@U) (|#$T1@@28| T@U) (|#$T2@@9| T@U) (|#$R@@57| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@44|) TyType) (= (type |#$T1@@28|) TyType)) (= (type |#$T2@@9|) TyType)) (= (type |#$R@@57|) TyType)) (= (Tclass._System.___hPartialFunc3_3 (Tclass._System.___hPartialFunc3 |#$T0@@44| |#$T1@@28| |#$T2@@9| |#$R@@57|)) |#$R@@57|))
 :qid |unknown.0:0|
 :skolemid |813|
 :pattern ( (Tclass._System.___hPartialFunc3 |#$T0@@44| |#$T1@@28| |#$T2@@9| |#$R@@57|))
)))
(assert (forall ((|#$T0@@45| T@U) (|#$T1@@29| T@U) (|#$T2@@10| T@U) (|#$R@@58| T@U) (bx@@63 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@45|) TyType) (= (type |#$T1@@29|) TyType)) (= (type |#$T2@@10|) TyType)) (= (type |#$R@@58|) TyType)) (= (type bx@@63) BoxType)) ($IsBox bx@@63 (Tclass._System.___hPartialFunc3 |#$T0@@45| |#$T1@@29| |#$T2@@10| |#$R@@58|))) (and (= ($Box ($Unbox HandleTypeType bx@@63)) bx@@63) ($Is ($Unbox HandleTypeType bx@@63) (Tclass._System.___hPartialFunc3 |#$T0@@45| |#$T1@@29| |#$T2@@10| |#$R@@58|))))
 :qid |unknown.0:0|
 :skolemid |814|
 :pattern ( ($IsBox bx@@63 (Tclass._System.___hPartialFunc3 |#$T0@@45| |#$T1@@29| |#$T2@@10| |#$R@@58|)))
)))
(assert (forall ((|#$T0@@46| T@U) (|#$T1@@30| T@U) (|#$T2@@11| T@U) (|#$R@@59| T@U) (|f#0@@11| T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@46|) TyType) (= (type |#$T1@@30|) TyType)) (= (type |#$T2@@11|) TyType)) (= (type |#$R@@59|) TyType)) (= (type |f#0@@11|) HandleTypeType)) (and (=> ($Is |f#0@@11| (Tclass._System.___hPartialFunc3 |#$T0@@46| |#$T1@@30| |#$T2@@11| |#$R@@59|)) (and ($Is |f#0@@11| (Tclass._System.___hFunc3 |#$T0@@46| |#$T1@@30| |#$T2@@11| |#$R@@59|)) (forall ((|x0#0@@7| T@U) (|x1#0@@3| T@U) (|x2#0| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@7|) BoxType) (= (type |x1#0@@3|) BoxType)) (= (type |x2#0|) BoxType)) (and (and ($IsBox |x0#0@@7| |#$T0@@46|) ($IsBox |x1#0@@3| |#$T1@@30|)) ($IsBox |x2#0| |#$T2@@11|))) (|Set#Equal| (Reads3 |#$T0@@46| |#$T1@@30| |#$T2@@11| |#$R@@59| $OneHeap |f#0@@11| |x0#0@@7| |x1#0@@3| |x2#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |815|
 :no-pattern (type |x0#0@@7|)
 :no-pattern (type |x1#0@@3|)
 :no-pattern (type |x2#0|)
 :no-pattern (U_2_int |x0#0@@7|)
 :no-pattern (U_2_bool |x0#0@@7|)
 :no-pattern (U_2_int |x1#0@@3|)
 :no-pattern (U_2_bool |x1#0@@3|)
 :no-pattern (U_2_int |x2#0|)
 :no-pattern (U_2_bool |x2#0|)
)))) (=> (and ($Is |f#0@@11| (Tclass._System.___hFunc3 |#$T0@@46| |#$T1@@30| |#$T2@@11| |#$R@@59|)) (forall ((|x0#0@@8| T@U) (|x1#0@@4| T@U) (|x2#0@@0| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@8|) BoxType) (= (type |x1#0@@4|) BoxType)) (= (type |x2#0@@0|) BoxType)) (and (and ($IsBox |x0#0@@8| |#$T0@@46|) ($IsBox |x1#0@@4| |#$T1@@30|)) ($IsBox |x2#0@@0| |#$T2@@11|))) (|Set#Equal| (Reads3 |#$T0@@46| |#$T1@@30| |#$T2@@11| |#$R@@59| $OneHeap |f#0@@11| |x0#0@@8| |x1#0@@4| |x2#0@@0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |815|
 :no-pattern (type |x0#0@@8|)
 :no-pattern (type |x1#0@@4|)
 :no-pattern (type |x2#0@@0|)
 :no-pattern (U_2_int |x0#0@@8|)
 :no-pattern (U_2_bool |x0#0@@8|)
 :no-pattern (U_2_int |x1#0@@4|)
 :no-pattern (U_2_bool |x1#0@@4|)
 :no-pattern (U_2_int |x2#0@@0|)
 :no-pattern (U_2_bool |x2#0@@0|)
))) ($Is |f#0@@11| (Tclass._System.___hPartialFunc3 |#$T0@@46| |#$T1@@30| |#$T2@@11| |#$R@@59|)))))
 :qid |unknown.0:0|
 :skolemid |816|
 :pattern ( ($Is |f#0@@11| (Tclass._System.___hPartialFunc3 |#$T0@@46| |#$T1@@30| |#$T2@@11| |#$R@@59|)))
)))
(assert (forall ((|#$T0@@47| T@U) (|#$T1@@31| T@U) (|#$T2@@12| T@U) (|#$R@@60| T@U) (|f#0@@12| T@U) ($h@@13 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@47|) TyType) (= (type |#$T1@@31|) TyType)) (= (type |#$T2@@12|) TyType)) (= (type |#$R@@60|) TyType)) (= (type |f#0@@12|) HandleTypeType)) (= (type $h@@13) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@12| (Tclass._System.___hPartialFunc3 |#$T0@@47| |#$T1@@31| |#$T2@@12| |#$R@@60|) $h@@13) ($IsAlloc |f#0@@12| (Tclass._System.___hFunc3 |#$T0@@47| |#$T1@@31| |#$T2@@12| |#$R@@60|) $h@@13)) (=> ($IsAlloc |f#0@@12| (Tclass._System.___hFunc3 |#$T0@@47| |#$T1@@31| |#$T2@@12| |#$R@@60|) $h@@13) ($IsAlloc |f#0@@12| (Tclass._System.___hPartialFunc3 |#$T0@@47| |#$T1@@31| |#$T2@@12| |#$R@@60|) $h@@13))))
 :qid |unknown.0:0|
 :skolemid |817|
 :pattern ( ($IsAlloc |f#0@@12| (Tclass._System.___hPartialFunc3 |#$T0@@47| |#$T1@@31| |#$T2@@12| |#$R@@60|) $h@@13))
)))
(assert (forall ((arg0@@181 T@U) (arg1@@87 T@U) (arg2@@45 T@U) (arg3@@24 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3 arg0@@181 arg1@@87 arg2@@45 arg3@@24)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3|
 :pattern ( (Tclass._System.___hTotalFunc3 arg0@@181 arg1@@87 arg2@@45 arg3@@24))
)))
(assert (forall ((|#$T0@@48| T@U) (|#$T1@@32| T@U) (|#$T2@@13| T@U) (|#$R@@61| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@48|) TyType) (= (type |#$T1@@32|) TyType)) (= (type |#$T2@@13|) TyType)) (= (type |#$R@@61|) TyType)) (= (Tag (Tclass._System.___hTotalFunc3 |#$T0@@48| |#$T1@@32| |#$T2@@13| |#$R@@61|)) Tagclass._System.___hTotalFunc3))
 :qid |unknown.0:0|
 :skolemid |818|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@48| |#$T1@@32| |#$T2@@13| |#$R@@61|))
)))
(assert (forall ((arg0@@182 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_0 arg0@@182)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_0|
 :pattern ( (Tclass._System.___hTotalFunc3_0 arg0@@182))
)))
(assert (forall ((|#$T0@@49| T@U) (|#$T1@@33| T@U) (|#$T2@@14| T@U) (|#$R@@62| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@49|) TyType) (= (type |#$T1@@33|) TyType)) (= (type |#$T2@@14|) TyType)) (= (type |#$R@@62|) TyType)) (= (Tclass._System.___hTotalFunc3_0 (Tclass._System.___hTotalFunc3 |#$T0@@49| |#$T1@@33| |#$T2@@14| |#$R@@62|)) |#$T0@@49|))
 :qid |unknown.0:0|
 :skolemid |819|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@49| |#$T1@@33| |#$T2@@14| |#$R@@62|))
)))
(assert (forall ((arg0@@183 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_1 arg0@@183)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_1|
 :pattern ( (Tclass._System.___hTotalFunc3_1 arg0@@183))
)))
(assert (forall ((|#$T0@@50| T@U) (|#$T1@@34| T@U) (|#$T2@@15| T@U) (|#$R@@63| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@50|) TyType) (= (type |#$T1@@34|) TyType)) (= (type |#$T2@@15|) TyType)) (= (type |#$R@@63|) TyType)) (= (Tclass._System.___hTotalFunc3_1 (Tclass._System.___hTotalFunc3 |#$T0@@50| |#$T1@@34| |#$T2@@15| |#$R@@63|)) |#$T1@@34|))
 :qid |unknown.0:0|
 :skolemid |820|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@50| |#$T1@@34| |#$T2@@15| |#$R@@63|))
)))
(assert (forall ((arg0@@184 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_2 arg0@@184)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_2|
 :pattern ( (Tclass._System.___hTotalFunc3_2 arg0@@184))
)))
(assert (forall ((|#$T0@@51| T@U) (|#$T1@@35| T@U) (|#$T2@@16| T@U) (|#$R@@64| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@51|) TyType) (= (type |#$T1@@35|) TyType)) (= (type |#$T2@@16|) TyType)) (= (type |#$R@@64|) TyType)) (= (Tclass._System.___hTotalFunc3_2 (Tclass._System.___hTotalFunc3 |#$T0@@51| |#$T1@@35| |#$T2@@16| |#$R@@64|)) |#$T2@@16|))
 :qid |unknown.0:0|
 :skolemid |821|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@51| |#$T1@@35| |#$T2@@16| |#$R@@64|))
)))
(assert (forall ((arg0@@185 T@U) ) (! (= (type (Tclass._System.___hTotalFunc3_3 arg0@@185)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc3_3|
 :pattern ( (Tclass._System.___hTotalFunc3_3 arg0@@185))
)))
(assert (forall ((|#$T0@@52| T@U) (|#$T1@@36| T@U) (|#$T2@@17| T@U) (|#$R@@65| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@52|) TyType) (= (type |#$T1@@36|) TyType)) (= (type |#$T2@@17|) TyType)) (= (type |#$R@@65|) TyType)) (= (Tclass._System.___hTotalFunc3_3 (Tclass._System.___hTotalFunc3 |#$T0@@52| |#$T1@@36| |#$T2@@17| |#$R@@65|)) |#$R@@65|))
 :qid |unknown.0:0|
 :skolemid |822|
 :pattern ( (Tclass._System.___hTotalFunc3 |#$T0@@52| |#$T1@@36| |#$T2@@17| |#$R@@65|))
)))
(assert (forall ((|#$T0@@53| T@U) (|#$T1@@37| T@U) (|#$T2@@18| T@U) (|#$R@@66| T@U) (bx@@64 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@53|) TyType) (= (type |#$T1@@37|) TyType)) (= (type |#$T2@@18|) TyType)) (= (type |#$R@@66|) TyType)) (= (type bx@@64) BoxType)) ($IsBox bx@@64 (Tclass._System.___hTotalFunc3 |#$T0@@53| |#$T1@@37| |#$T2@@18| |#$R@@66|))) (and (= ($Box ($Unbox HandleTypeType bx@@64)) bx@@64) ($Is ($Unbox HandleTypeType bx@@64) (Tclass._System.___hTotalFunc3 |#$T0@@53| |#$T1@@37| |#$T2@@18| |#$R@@66|))))
 :qid |unknown.0:0|
 :skolemid |823|
 :pattern ( ($IsBox bx@@64 (Tclass._System.___hTotalFunc3 |#$T0@@53| |#$T1@@37| |#$T2@@18| |#$R@@66|)))
)))
(assert (forall ((|#$T0@@54| T@U) (|#$T1@@38| T@U) (|#$T2@@19| T@U) (|#$R@@67| T@U) (|f#0@@13| T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@54|) TyType) (= (type |#$T1@@38|) TyType)) (= (type |#$T2@@19|) TyType)) (= (type |#$R@@67|) TyType)) (= (type |f#0@@13|) HandleTypeType)) (and (=> ($Is |f#0@@13| (Tclass._System.___hTotalFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@19| |#$R@@67|)) (and ($Is |f#0@@13| (Tclass._System.___hPartialFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@19| |#$R@@67|)) (forall ((|x0#0@@9| T@U) (|x1#0@@5| T@U) (|x2#0@@1| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@9|) BoxType) (= (type |x1#0@@5|) BoxType)) (= (type |x2#0@@1|) BoxType)) (and (and ($IsBox |x0#0@@9| |#$T0@@54|) ($IsBox |x1#0@@5| |#$T1@@38|)) ($IsBox |x2#0@@1| |#$T2@@19|))) (Requires3 |#$T0@@54| |#$T1@@38| |#$T2@@19| |#$R@@67| $OneHeap |f#0@@13| |x0#0@@9| |x1#0@@5| |x2#0@@1|))
 :qid |unknown.0:0|
 :skolemid |824|
 :no-pattern (type |x0#0@@9|)
 :no-pattern (type |x1#0@@5|)
 :no-pattern (type |x2#0@@1|)
 :no-pattern (U_2_int |x0#0@@9|)
 :no-pattern (U_2_bool |x0#0@@9|)
 :no-pattern (U_2_int |x1#0@@5|)
 :no-pattern (U_2_bool |x1#0@@5|)
 :no-pattern (U_2_int |x2#0@@1|)
 :no-pattern (U_2_bool |x2#0@@1|)
)))) (=> (and ($Is |f#0@@13| (Tclass._System.___hPartialFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@19| |#$R@@67|)) (forall ((|x0#0@@10| T@U) (|x1#0@@6| T@U) (|x2#0@@2| T@U) ) (!  (=> (and (and (and (= (type |x0#0@@10|) BoxType) (= (type |x1#0@@6|) BoxType)) (= (type |x2#0@@2|) BoxType)) (and (and ($IsBox |x0#0@@10| |#$T0@@54|) ($IsBox |x1#0@@6| |#$T1@@38|)) ($IsBox |x2#0@@2| |#$T2@@19|))) (Requires3 |#$T0@@54| |#$T1@@38| |#$T2@@19| |#$R@@67| $OneHeap |f#0@@13| |x0#0@@10| |x1#0@@6| |x2#0@@2|))
 :qid |unknown.0:0|
 :skolemid |824|
 :no-pattern (type |x0#0@@10|)
 :no-pattern (type |x1#0@@6|)
 :no-pattern (type |x2#0@@2|)
 :no-pattern (U_2_int |x0#0@@10|)
 :no-pattern (U_2_bool |x0#0@@10|)
 :no-pattern (U_2_int |x1#0@@6|)
 :no-pattern (U_2_bool |x1#0@@6|)
 :no-pattern (U_2_int |x2#0@@2|)
 :no-pattern (U_2_bool |x2#0@@2|)
))) ($Is |f#0@@13| (Tclass._System.___hTotalFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@19| |#$R@@67|)))))
 :qid |unknown.0:0|
 :skolemid |825|
 :pattern ( ($Is |f#0@@13| (Tclass._System.___hTotalFunc3 |#$T0@@54| |#$T1@@38| |#$T2@@19| |#$R@@67|)))
)))
(assert (forall ((|#$T0@@55| T@U) (|#$T1@@39| T@U) (|#$T2@@20| T@U) (|#$R@@68| T@U) (|f#0@@14| T@U) ($h@@14 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@55|) TyType) (= (type |#$T1@@39|) TyType)) (= (type |#$T2@@20|) TyType)) (= (type |#$R@@68|) TyType)) (= (type |f#0@@14|) HandleTypeType)) (= (type $h@@14) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@14| (Tclass._System.___hTotalFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@20| |#$R@@68|) $h@@14) ($IsAlloc |f#0@@14| (Tclass._System.___hPartialFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@20| |#$R@@68|) $h@@14)) (=> ($IsAlloc |f#0@@14| (Tclass._System.___hPartialFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@20| |#$R@@68|) $h@@14) ($IsAlloc |f#0@@14| (Tclass._System.___hTotalFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@20| |#$R@@68|) $h@@14))))
 :qid |unknown.0:0|
 :skolemid |826|
 :pattern ( ($IsAlloc |f#0@@14| (Tclass._System.___hTotalFunc3 |#$T0@@55| |#$T1@@39| |#$T2@@20| |#$R@@68|) $h@@14))
)))
(assert  (and (forall ((arg0@@186 T@U) ) (! (= (type (DatatypeCtorId arg0@@186)) DtCtorIdType)
 :qid |funType:DatatypeCtorId|
 :pattern ( (DatatypeCtorId arg0@@186))
)) (= (type |#_System._tuple#0._#Make0|) DatatypeTypeType)))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (forall ((d@@0 T@U) ) (!  (=> (= (type d@@0) DatatypeTypeType) (and (=> (_System.Tuple0.___hMake0_q d@@0) (= (DatatypeCtorId d@@0) |##_System._tuple#0._#Make0|)) (=> (= (DatatypeCtorId d@@0) |##_System._tuple#0._#Make0|) (_System.Tuple0.___hMake0_q d@@0))))
 :qid |unknown.0:0|
 :skolemid |827|
 :pattern ( (_System.Tuple0.___hMake0_q d@@0))
)))
(assert (forall ((d@@1 T@U) ) (!  (=> (and (= (type d@@1) DatatypeTypeType) (_System.Tuple0.___hMake0_q d@@1)) (= d@@1 |#_System._tuple#0._#Make0|))
 :qid |unknown.0:0|
 :skolemid |828|
 :pattern ( (_System.Tuple0.___hMake0_q d@@1))
)))
(assert (= (type Tclass._System.Tuple0) TyType))
(assert (= (Tag Tclass._System.Tuple0) Tagclass._System.Tuple0))
(assert (forall ((bx@@65 T@U) ) (!  (=> (and (= (type bx@@65) BoxType) ($IsBox bx@@65 Tclass._System.Tuple0)) (and (= ($Box ($Unbox DatatypeTypeType bx@@65)) bx@@65) ($Is ($Unbox DatatypeTypeType bx@@65) Tclass._System.Tuple0)))
 :qid |unknown.0:0|
 :skolemid |829|
 :pattern ( ($IsBox bx@@65 Tclass._System.Tuple0))
)))
(assert ($Is |#_System._tuple#0._#Make0| Tclass._System.Tuple0))
(assert (forall (($h@@15 T@U) ) (!  (=> (and (= (type $h@@15) (MapType0Type refType MapType1Type)) ($IsGoodHeap $h@@15)) ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@15))
 :qid |DafnyPre.515:12|
 :skolemid |830|
 :pattern ( ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@15))
)))
(assert (= |#_System._tuple#0._#Make0| (Lit |#_System._tuple#0._#Make0|)))
(assert (forall ((d@@2 T@U) ) (!  (=> (and (= (type d@@2) DatatypeTypeType) (|$IsA#_System.Tuple0| d@@2)) (_System.Tuple0.___hMake0_q d@@2))
 :qid |unknown.0:0|
 :skolemid |831|
 :pattern ( (|$IsA#_System.Tuple0| d@@2))
)))
(assert (forall ((d@@3 T@U) ) (!  (=> (and (= (type d@@3) DatatypeTypeType) ($Is d@@3 Tclass._System.Tuple0)) (_System.Tuple0.___hMake0_q d@@3))
 :qid |unknown.0:0|
 :skolemid |832|
 :pattern ( (_System.Tuple0.___hMake0_q d@@3) ($Is d@@3 Tclass._System.Tuple0))
)))
(assert (forall ((a@@103 T@U) (b@@58 T@U) ) (!  (=> (and (and (= (type a@@103) DatatypeTypeType) (= (type b@@58) DatatypeTypeType)) true) (and (=> (|_System.Tuple0#Equal| a@@103 b@@58) true) (=> true (|_System.Tuple0#Equal| a@@103 b@@58))))
 :qid |unknown.0:0|
 :skolemid |833|
 :pattern ( (|_System.Tuple0#Equal| a@@103 b@@58))
)))
(assert (forall ((a@@104 T@U) (b@@59 T@U) ) (!  (=> (and (= (type a@@104) DatatypeTypeType) (= (type b@@59) DatatypeTypeType)) (and (=> (|_System.Tuple0#Equal| a@@104 b@@59) (= a@@104 b@@59)) (=> (= a@@104 b@@59) (|_System.Tuple0#Equal| a@@104 b@@59))))
 :qid |unknown.0:0|
 :skolemid |834|
 :pattern ( (|_System.Tuple0#Equal| a@@104 b@@59))
)))
(assert (forall ((arg0@@187 T@U) (arg1@@88 T@U) (arg2@@46 T@U) (arg3@@25 T@U) (arg4@@14 T@U) (arg5@@4 T@U) ) (! (= (type (Tclass._System.___hFunc5 arg0@@187 arg1@@88 arg2@@46 arg3@@25 arg4@@14 arg5@@4)) TyType)
 :qid |funType:Tclass._System.___hFunc5|
 :pattern ( (Tclass._System.___hFunc5 arg0@@187 arg1@@88 arg2@@46 arg3@@25 arg4@@14 arg5@@4))
)))
(assert (forall ((|#$T0@@56| T@U) (|#$T1@@40| T@U) (|#$T2@@21| T@U) (|#$T3| T@U) (|#$T4| T@U) (|#$R@@69| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@56|) TyType) (= (type |#$T1@@40|) TyType)) (= (type |#$T2@@21|) TyType)) (= (type |#$T3|) TyType)) (= (type |#$T4|) TyType)) (= (type |#$R@@69|) TyType)) (= (Tag (Tclass._System.___hFunc5 |#$T0@@56| |#$T1@@40| |#$T2@@21| |#$T3| |#$T4| |#$R@@69|)) Tagclass._System.___hFunc5))
 :qid |unknown.0:0|
 :skolemid |835|
 :pattern ( (Tclass._System.___hFunc5 |#$T0@@56| |#$T1@@40| |#$T2@@21| |#$T3| |#$T4| |#$R@@69|))
)))
(assert (forall ((arg0@@188 T@U) ) (! (= (type (Tclass._System.___hFunc5_0 arg0@@188)) TyType)
 :qid |funType:Tclass._System.___hFunc5_0|
 :pattern ( (Tclass._System.___hFunc5_0 arg0@@188))
)))
(assert (forall ((|#$T0@@57| T@U) (|#$T1@@41| T@U) (|#$T2@@22| T@U) (|#$T3@@0| T@U) (|#$T4@@0| T@U) (|#$R@@70| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@57|) TyType) (= (type |#$T1@@41|) TyType)) (= (type |#$T2@@22|) TyType)) (= (type |#$T3@@0|) TyType)) (= (type |#$T4@@0|) TyType)) (= (type |#$R@@70|) TyType)) (= (Tclass._System.___hFunc5_0 (Tclass._System.___hFunc5 |#$T0@@57| |#$T1@@41| |#$T2@@22| |#$T3@@0| |#$T4@@0| |#$R@@70|)) |#$T0@@57|))
 :qid |unknown.0:0|
 :skolemid |836|
 :pattern ( (Tclass._System.___hFunc5 |#$T0@@57| |#$T1@@41| |#$T2@@22| |#$T3@@0| |#$T4@@0| |#$R@@70|))
)))
(assert (forall ((arg0@@189 T@U) ) (! (= (type (Tclass._System.___hFunc5_1 arg0@@189)) TyType)
 :qid |funType:Tclass._System.___hFunc5_1|
 :pattern ( (Tclass._System.___hFunc5_1 arg0@@189))
)))
(assert (forall ((|#$T0@@58| T@U) (|#$T1@@42| T@U) (|#$T2@@23| T@U) (|#$T3@@1| T@U) (|#$T4@@1| T@U) (|#$R@@71| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@58|) TyType) (= (type |#$T1@@42|) TyType)) (= (type |#$T2@@23|) TyType)) (= (type |#$T3@@1|) TyType)) (= (type |#$T4@@1|) TyType)) (= (type |#$R@@71|) TyType)) (= (Tclass._System.___hFunc5_1 (Tclass._System.___hFunc5 |#$T0@@58| |#$T1@@42| |#$T2@@23| |#$T3@@1| |#$T4@@1| |#$R@@71|)) |#$T1@@42|))
 :qid |unknown.0:0|
 :skolemid |837|
 :pattern ( (Tclass._System.___hFunc5 |#$T0@@58| |#$T1@@42| |#$T2@@23| |#$T3@@1| |#$T4@@1| |#$R@@71|))
)))
(assert (forall ((arg0@@190 T@U) ) (! (= (type (Tclass._System.___hFunc5_2 arg0@@190)) TyType)
 :qid |funType:Tclass._System.___hFunc5_2|
 :pattern ( (Tclass._System.___hFunc5_2 arg0@@190))
)))
(assert (forall ((|#$T0@@59| T@U) (|#$T1@@43| T@U) (|#$T2@@24| T@U) (|#$T3@@2| T@U) (|#$T4@@2| T@U) (|#$R@@72| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@59|) TyType) (= (type |#$T1@@43|) TyType)) (= (type |#$T2@@24|) TyType)) (= (type |#$T3@@2|) TyType)) (= (type |#$T4@@2|) TyType)) (= (type |#$R@@72|) TyType)) (= (Tclass._System.___hFunc5_2 (Tclass._System.___hFunc5 |#$T0@@59| |#$T1@@43| |#$T2@@24| |#$T3@@2| |#$T4@@2| |#$R@@72|)) |#$T2@@24|))
 :qid |unknown.0:0|
 :skolemid |838|
 :pattern ( (Tclass._System.___hFunc5 |#$T0@@59| |#$T1@@43| |#$T2@@24| |#$T3@@2| |#$T4@@2| |#$R@@72|))
)))
(assert (forall ((arg0@@191 T@U) ) (! (= (type (Tclass._System.___hFunc5_3 arg0@@191)) TyType)
 :qid |funType:Tclass._System.___hFunc5_3|
 :pattern ( (Tclass._System.___hFunc5_3 arg0@@191))
)))
(assert (forall ((|#$T0@@60| T@U) (|#$T1@@44| T@U) (|#$T2@@25| T@U) (|#$T3@@3| T@U) (|#$T4@@3| T@U) (|#$R@@73| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@60|) TyType) (= (type |#$T1@@44|) TyType)) (= (type |#$T2@@25|) TyType)) (= (type |#$T3@@3|) TyType)) (= (type |#$T4@@3|) TyType)) (= (type |#$R@@73|) TyType)) (= (Tclass._System.___hFunc5_3 (Tclass._System.___hFunc5 |#$T0@@60| |#$T1@@44| |#$T2@@25| |#$T3@@3| |#$T4@@3| |#$R@@73|)) |#$T3@@3|))
 :qid |unknown.0:0|
 :skolemid |839|
 :pattern ( (Tclass._System.___hFunc5 |#$T0@@60| |#$T1@@44| |#$T2@@25| |#$T3@@3| |#$T4@@3| |#$R@@73|))
)))
(assert (forall ((arg0@@192 T@U) ) (! (= (type (Tclass._System.___hFunc5_4 arg0@@192)) TyType)
 :qid |funType:Tclass._System.___hFunc5_4|
 :pattern ( (Tclass._System.___hFunc5_4 arg0@@192))
)))
(assert (forall ((|#$T0@@61| T@U) (|#$T1@@45| T@U) (|#$T2@@26| T@U) (|#$T3@@4| T@U) (|#$T4@@4| T@U) (|#$R@@74| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@61|) TyType) (= (type |#$T1@@45|) TyType)) (= (type |#$T2@@26|) TyType)) (= (type |#$T3@@4|) TyType)) (= (type |#$T4@@4|) TyType)) (= (type |#$R@@74|) TyType)) (= (Tclass._System.___hFunc5_4 (Tclass._System.___hFunc5 |#$T0@@61| |#$T1@@45| |#$T2@@26| |#$T3@@4| |#$T4@@4| |#$R@@74|)) |#$T4@@4|))
 :qid |unknown.0:0|
 :skolemid |840|
 :pattern ( (Tclass._System.___hFunc5 |#$T0@@61| |#$T1@@45| |#$T2@@26| |#$T3@@4| |#$T4@@4| |#$R@@74|))
)))
(assert (forall ((arg0@@193 T@U) ) (! (= (type (Tclass._System.___hFunc5_5 arg0@@193)) TyType)
 :qid |funType:Tclass._System.___hFunc5_5|
 :pattern ( (Tclass._System.___hFunc5_5 arg0@@193))
)))
(assert (forall ((|#$T0@@62| T@U) (|#$T1@@46| T@U) (|#$T2@@27| T@U) (|#$T3@@5| T@U) (|#$T4@@5| T@U) (|#$R@@75| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@62|) TyType) (= (type |#$T1@@46|) TyType)) (= (type |#$T2@@27|) TyType)) (= (type |#$T3@@5|) TyType)) (= (type |#$T4@@5|) TyType)) (= (type |#$R@@75|) TyType)) (= (Tclass._System.___hFunc5_5 (Tclass._System.___hFunc5 |#$T0@@62| |#$T1@@46| |#$T2@@27| |#$T3@@5| |#$T4@@5| |#$R@@75|)) |#$R@@75|))
 :qid |unknown.0:0|
 :skolemid |841|
 :pattern ( (Tclass._System.___hFunc5 |#$T0@@62| |#$T1@@46| |#$T2@@27| |#$T3@@5| |#$T4@@5| |#$R@@75|))
)))
(assert (forall ((|#$T0@@63| T@U) (|#$T1@@47| T@U) (|#$T2@@28| T@U) (|#$T3@@6| T@U) (|#$T4@@6| T@U) (|#$R@@76| T@U) (bx@@66 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type |#$T0@@63|) TyType) (= (type |#$T1@@47|) TyType)) (= (type |#$T2@@28|) TyType)) (= (type |#$T3@@6|) TyType)) (= (type |#$T4@@6|) TyType)) (= (type |#$R@@76|) TyType)) (= (type bx@@66) BoxType)) ($IsBox bx@@66 (Tclass._System.___hFunc5 |#$T0@@63| |#$T1@@47| |#$T2@@28| |#$T3@@6| |#$T4@@6| |#$R@@76|))) (and (= ($Box ($Unbox HandleTypeType bx@@66)) bx@@66) ($Is ($Unbox HandleTypeType bx@@66) (Tclass._System.___hFunc5 |#$T0@@63| |#$T1@@47| |#$T2@@28| |#$T3@@6| |#$T4@@6| |#$R@@76|))))
 :qid |unknown.0:0|
 :skolemid |842|
 :pattern ( ($IsBox bx@@66 (Tclass._System.___hFunc5 |#$T0@@63| |#$T1@@47| |#$T2@@28| |#$T3@@6| |#$T4@@6| |#$R@@76|)))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (forall ((arg0@@194 T@T) (arg1@@89 T@T) (arg2@@47 T@T) (arg3@@26 T@T) (arg4@@15 T@T) (arg5@@5 T@T) (arg6@@3 T@T) ) (! (= (Ctor (MapType5Type arg0@@194 arg1@@89 arg2@@47 arg3@@26 arg4@@15 arg5@@5 arg6@@3)) 26)
 :qid |ctor:MapType5Type|
)) (forall ((arg0@@195 T@T) (arg1@@90 T@T) (arg2@@48 T@T) (arg3@@27 T@T) (arg4@@16 T@T) (arg5@@6 T@T) (arg6@@4 T@T) ) (! (= (MapType5TypeInv0 (MapType5Type arg0@@195 arg1@@90 arg2@@48 arg3@@27 arg4@@16 arg5@@6 arg6@@4)) arg0@@195)
 :qid |typeInv:MapType5TypeInv0|
 :pattern ( (MapType5Type arg0@@195 arg1@@90 arg2@@48 arg3@@27 arg4@@16 arg5@@6 arg6@@4))
))) (forall ((arg0@@196 T@T) (arg1@@91 T@T) (arg2@@49 T@T) (arg3@@28 T@T) (arg4@@17 T@T) (arg5@@7 T@T) (arg6@@5 T@T) ) (! (= (MapType5TypeInv1 (MapType5Type arg0@@196 arg1@@91 arg2@@49 arg3@@28 arg4@@17 arg5@@7 arg6@@5)) arg1@@91)
 :qid |typeInv:MapType5TypeInv1|
 :pattern ( (MapType5Type arg0@@196 arg1@@91 arg2@@49 arg3@@28 arg4@@17 arg5@@7 arg6@@5))
))) (forall ((arg0@@197 T@T) (arg1@@92 T@T) (arg2@@50 T@T) (arg3@@29 T@T) (arg4@@18 T@T) (arg5@@8 T@T) (arg6@@6 T@T) ) (! (= (MapType5TypeInv2 (MapType5Type arg0@@197 arg1@@92 arg2@@50 arg3@@29 arg4@@18 arg5@@8 arg6@@6)) arg2@@50)
 :qid |typeInv:MapType5TypeInv2|
 :pattern ( (MapType5Type arg0@@197 arg1@@92 arg2@@50 arg3@@29 arg4@@18 arg5@@8 arg6@@6))
))) (forall ((arg0@@198 T@T) (arg1@@93 T@T) (arg2@@51 T@T) (arg3@@30 T@T) (arg4@@19 T@T) (arg5@@9 T@T) (arg6@@7 T@T) ) (! (= (MapType5TypeInv3 (MapType5Type arg0@@198 arg1@@93 arg2@@51 arg3@@30 arg4@@19 arg5@@9 arg6@@7)) arg3@@30)
 :qid |typeInv:MapType5TypeInv3|
 :pattern ( (MapType5Type arg0@@198 arg1@@93 arg2@@51 arg3@@30 arg4@@19 arg5@@9 arg6@@7))
))) (forall ((arg0@@199 T@T) (arg1@@94 T@T) (arg2@@52 T@T) (arg3@@31 T@T) (arg4@@20 T@T) (arg5@@10 T@T) (arg6@@8 T@T) ) (! (= (MapType5TypeInv4 (MapType5Type arg0@@199 arg1@@94 arg2@@52 arg3@@31 arg4@@20 arg5@@10 arg6@@8)) arg4@@20)
 :qid |typeInv:MapType5TypeInv4|
 :pattern ( (MapType5Type arg0@@199 arg1@@94 arg2@@52 arg3@@31 arg4@@20 arg5@@10 arg6@@8))
))) (forall ((arg0@@200 T@T) (arg1@@95 T@T) (arg2@@53 T@T) (arg3@@32 T@T) (arg4@@21 T@T) (arg5@@11 T@T) (arg6@@9 T@T) ) (! (= (MapType5TypeInv5 (MapType5Type arg0@@200 arg1@@95 arg2@@53 arg3@@32 arg4@@21 arg5@@11 arg6@@9)) arg5@@11)
 :qid |typeInv:MapType5TypeInv5|
 :pattern ( (MapType5Type arg0@@200 arg1@@95 arg2@@53 arg3@@32 arg4@@21 arg5@@11 arg6@@9))
))) (forall ((arg0@@201 T@T) (arg1@@96 T@T) (arg2@@54 T@T) (arg3@@33 T@T) (arg4@@22 T@T) (arg5@@12 T@T) (arg6@@10 T@T) ) (! (= (MapType5TypeInv6 (MapType5Type arg0@@201 arg1@@96 arg2@@54 arg3@@33 arg4@@22 arg5@@12 arg6@@10)) arg6@@10)
 :qid |typeInv:MapType5TypeInv6|
 :pattern ( (MapType5Type arg0@@201 arg1@@96 arg2@@54 arg3@@33 arg4@@22 arg5@@12 arg6@@10))
))) (forall ((arg0@@202 T@U) (arg1@@97 T@U) (arg2@@55 T@U) (arg3@@34 T@U) (arg4@@23 T@U) (arg5@@13 T@U) (arg6@@11 T@U) ) (! (let ((aVar6 (MapType5TypeInv6 (type arg0@@202))))
(= (type (MapType5Select arg0@@202 arg1@@97 arg2@@55 arg3@@34 arg4@@23 arg5@@13 arg6@@11)) aVar6))
 :qid |funType:MapType5Select|
 :pattern ( (MapType5Select arg0@@202 arg1@@97 arg2@@55 arg3@@34 arg4@@23 arg5@@13 arg6@@11))
))) (forall ((arg0@@203 T@U) (arg1@@98 T@U) (arg2@@56 T@U) (arg3@@35 T@U) (arg4@@24 T@U) (arg5@@14 T@U) (arg6@@12 T@U) (arg7@@1 T@U) ) (! (let ((aVar6@@0 (type arg7@@1)))
(let ((aVar5 (type arg6@@12)))
(let ((aVar4@@2 (type arg5@@14)))
(let ((aVar3@@3 (type arg4@@24)))
(let ((aVar2@@4 (type arg3@@35)))
(let ((aVar1@@5 (type arg2@@56)))
(let ((aVar0@@3 (type arg1@@98)))
(= (type (MapType5Store arg0@@203 arg1@@98 arg2@@56 arg3@@35 arg4@@24 arg5@@14 arg6@@12 arg7@@1)) (MapType5Type aVar0@@3 aVar1@@5 aVar2@@4 aVar3@@3 aVar4@@2 aVar5 aVar6@@0)))))))))
 :qid |funType:MapType5Store|
 :pattern ( (MapType5Store arg0@@203 arg1@@98 arg2@@56 arg3@@35 arg4@@24 arg5@@14 arg6@@12 arg7@@1))
))) (forall ((m@@42 T@U) (x0@@20 T@U) (x1@@14 T@U) (x2@@10 T@U) (x3@@5 T@U) (x4 T@U) (x5 T@U) (val@@21 T@U) ) (! (let ((aVar6@@1 (MapType5TypeInv6 (type m@@42))))
 (=> (= (type val@@21) aVar6@@1) (= (MapType5Select (MapType5Store m@@42 x0@@20 x1@@14 x2@@10 x3@@5 x4 x5 val@@21) x0@@20 x1@@14 x2@@10 x3@@5 x4 x5) val@@21)))
 :qid |mapAx0:MapType5Select|
 :weight 0
))) (and (and (and (and (and (and (forall ((val@@22 T@U) (m@@43 T@U) (x0@@21 T@U) (x1@@15 T@U) (x2@@11 T@U) (x3@@6 T@U) (x4@@0 T@U) (x5@@0 T@U) (y0@@15 T@U) (y1@@11 T@U) (y2@@8 T@U) (y3@@4 T@U) (y4 T@U) (y5 T@U) ) (!  (or (= x0@@21 y0@@15) (= (MapType5Select (MapType5Store m@@43 x0@@21 x1@@15 x2@@11 x3@@6 x4@@0 x5@@0 val@@22) y0@@15 y1@@11 y2@@8 y3@@4 y4 y5) (MapType5Select m@@43 y0@@15 y1@@11 y2@@8 y3@@4 y4 y5)))
 :qid |mapAx1:MapType5Select:0|
 :weight 0
)) (forall ((val@@23 T@U) (m@@44 T@U) (x0@@22 T@U) (x1@@16 T@U) (x2@@12 T@U) (x3@@7 T@U) (x4@@1 T@U) (x5@@1 T@U) (y0@@16 T@U) (y1@@12 T@U) (y2@@9 T@U) (y3@@5 T@U) (y4@@0 T@U) (y5@@0 T@U) ) (!  (or (= x1@@16 y1@@12) (= (MapType5Select (MapType5Store m@@44 x0@@22 x1@@16 x2@@12 x3@@7 x4@@1 x5@@1 val@@23) y0@@16 y1@@12 y2@@9 y3@@5 y4@@0 y5@@0) (MapType5Select m@@44 y0@@16 y1@@12 y2@@9 y3@@5 y4@@0 y5@@0)))
 :qid |mapAx1:MapType5Select:1|
 :weight 0
))) (forall ((val@@24 T@U) (m@@45 T@U) (x0@@23 T@U) (x1@@17 T@U) (x2@@13 T@U) (x3@@8 T@U) (x4@@2 T@U) (x5@@2 T@U) (y0@@17 T@U) (y1@@13 T@U) (y2@@10 T@U) (y3@@6 T@U) (y4@@1 T@U) (y5@@1 T@U) ) (!  (or (= x2@@13 y2@@10) (= (MapType5Select (MapType5Store m@@45 x0@@23 x1@@17 x2@@13 x3@@8 x4@@2 x5@@2 val@@24) y0@@17 y1@@13 y2@@10 y3@@6 y4@@1 y5@@1) (MapType5Select m@@45 y0@@17 y1@@13 y2@@10 y3@@6 y4@@1 y5@@1)))
 :qid |mapAx1:MapType5Select:2|
 :weight 0
))) (forall ((val@@25 T@U) (m@@46 T@U) (x0@@24 T@U) (x1@@18 T@U) (x2@@14 T@U) (x3@@9 T@U) (x4@@3 T@U) (x5@@3 T@U) (y0@@18 T@U) (y1@@14 T@U) (y2@@11 T@U) (y3@@7 T@U) (y4@@2 T@U) (y5@@2 T@U) ) (!  (or (= x3@@9 y3@@7) (= (MapType5Select (MapType5Store m@@46 x0@@24 x1@@18 x2@@14 x3@@9 x4@@3 x5@@3 val@@25) y0@@18 y1@@14 y2@@11 y3@@7 y4@@2 y5@@2) (MapType5Select m@@46 y0@@18 y1@@14 y2@@11 y3@@7 y4@@2 y5@@2)))
 :qid |mapAx1:MapType5Select:3|
 :weight 0
))) (forall ((val@@26 T@U) (m@@47 T@U) (x0@@25 T@U) (x1@@19 T@U) (x2@@15 T@U) (x3@@10 T@U) (x4@@4 T@U) (x5@@4 T@U) (y0@@19 T@U) (y1@@15 T@U) (y2@@12 T@U) (y3@@8 T@U) (y4@@3 T@U) (y5@@3 T@U) ) (!  (or (= x4@@4 y4@@3) (= (MapType5Select (MapType5Store m@@47 x0@@25 x1@@19 x2@@15 x3@@10 x4@@4 x5@@4 val@@26) y0@@19 y1@@15 y2@@12 y3@@8 y4@@3 y5@@3) (MapType5Select m@@47 y0@@19 y1@@15 y2@@12 y3@@8 y4@@3 y5@@3)))
 :qid |mapAx1:MapType5Select:4|
 :weight 0
))) (forall ((val@@27 T@U) (m@@48 T@U) (x0@@26 T@U) (x1@@20 T@U) (x2@@16 T@U) (x3@@11 T@U) (x4@@5 T@U) (x5@@5 T@U) (y0@@20 T@U) (y1@@16 T@U) (y2@@13 T@U) (y3@@9 T@U) (y4@@4 T@U) (y5@@4 T@U) ) (!  (or (= x5@@5 y5@@4) (= (MapType5Select (MapType5Store m@@48 x0@@26 x1@@20 x2@@16 x3@@11 x4@@5 x5@@5 val@@27) y0@@20 y1@@16 y2@@13 y3@@9 y4@@4 y5@@4) (MapType5Select m@@48 y0@@20 y1@@16 y2@@13 y3@@9 y4@@4 y5@@4)))
 :qid |mapAx1:MapType5Select:5|
 :weight 0
))) (forall ((val@@28 T@U) (m@@49 T@U) (x0@@27 T@U) (x1@@21 T@U) (x2@@17 T@U) (x3@@12 T@U) (x4@@6 T@U) (x5@@6 T@U) (y0@@21 T@U) (y1@@17 T@U) (y2@@14 T@U) (y3@@10 T@U) (y4@@5 T@U) (y5@@5 T@U) ) (!  (or true (= (MapType5Select (MapType5Store m@@49 x0@@27 x1@@21 x2@@17 x3@@12 x4@@6 x5@@6 val@@28) y0@@21 y1@@17 y2@@14 y3@@10 y4@@5 y5@@5) (MapType5Select m@@49 y0@@21 y1@@17 y2@@14 y3@@10 y4@@5 y5@@5)))
 :qid |mapAx2:MapType5Select|
 :weight 0
)))) (forall ((arg0@@204 T@U) (arg1@@99 T@U) (arg2@@57 T@U) (arg3@@36 T@U) (arg4@@25 T@U) (arg5@@15 T@U) (arg6@@13 T@U) (arg7@@2 T@U) (arg8@@1 T@U) (arg9 T@U) (arg10 T@U) (arg11 T@U) (arg12 T@U) ) (! (= (type (Apply5 arg0@@204 arg1@@99 arg2@@57 arg3@@36 arg4@@25 arg5@@15 arg6@@13 arg7@@2 arg8@@1 arg9 arg10 arg11 arg12)) BoxType)
 :qid |funType:Apply5|
 :pattern ( (Apply5 arg0@@204 arg1@@99 arg2@@57 arg3@@36 arg4@@25 arg5@@15 arg6@@13 arg7@@2 arg8@@1 arg9 arg10 arg11 arg12))
))) (forall ((arg0@@205 T@U) (arg1@@100 T@U) (arg2@@58 T@U) ) (! (= (type (Handle5 arg0@@205 arg1@@100 arg2@@58)) HandleTypeType)
 :qid |funType:Handle5|
 :pattern ( (Handle5 arg0@@205 arg1@@100 arg2@@58))
))))
(assert (forall ((t0@@72 T@U) (t1@@48 T@U) (t2@@29 T@U) (t3@@14 T@U) (t4 T@U) (t5 T@U) (heap@@21 T@U) (h@@48 T@U) (r@@26 T@U) (rd@@11 T@U) (bx0@@47 T@U) (bx1@@31 T@U) (bx2@@15 T@U) (bx3 T@U) (bx4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@72) TyType) (= (type t1@@48) TyType)) (= (type t2@@29) TyType)) (= (type t3@@14) TyType)) (= (type t4) TyType)) (= (type t5) TyType)) (= (type heap@@21) (MapType0Type refType MapType1Type))) (= (type h@@48) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType BoxType))) (= (type r@@26) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType boolType))) (= (type rd@@11) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@47) BoxType)) (= (type bx1@@31) BoxType)) (= (type bx2@@15) BoxType)) (= (type bx3) BoxType)) (= (type bx4) BoxType)) (= (Apply5 t0@@72 t1@@48 t2@@29 t3@@14 t4 t5 heap@@21 (Handle5 h@@48 r@@26 rd@@11) bx0@@47 bx1@@31 bx2@@15 bx3 bx4) (MapType5Select h@@48 heap@@21 bx0@@47 bx1@@31 bx2@@15 bx3 bx4)))
 :qid |unknown.0:0|
 :skolemid |843|
 :pattern ( (Apply5 t0@@72 t1@@48 t2@@29 t3@@14 t4 t5 heap@@21 (Handle5 h@@48 r@@26 rd@@11) bx0@@47 bx1@@31 bx2@@15 bx3 bx4))
)))
(assert (forall ((t0@@73 T@U) (t1@@49 T@U) (t2@@30 T@U) (t3@@15 T@U) (t4@@0 T@U) (t5@@0 T@U) (heap@@22 T@U) (h@@49 T@U) (r@@27 T@U) (rd@@12 T@U) (bx0@@48 T@U) (bx1@@32 T@U) (bx2@@16 T@U) (bx3@@0 T@U) (bx4@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@73) TyType) (= (type t1@@49) TyType)) (= (type t2@@30) TyType)) (= (type t3@@15) TyType)) (= (type t4@@0) TyType)) (= (type t5@@0) TyType)) (= (type heap@@22) (MapType0Type refType MapType1Type))) (= (type h@@49) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType BoxType))) (= (type r@@27) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType boolType))) (= (type rd@@12) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@48) BoxType)) (= (type bx1@@32) BoxType)) (= (type bx2@@16) BoxType)) (= (type bx3@@0) BoxType)) (= (type bx4@@0) BoxType)) (U_2_bool (MapType5Select r@@27 heap@@22 bx0@@48 bx1@@32 bx2@@16 bx3@@0 bx4@@0))) (Requires5 t0@@73 t1@@49 t2@@30 t3@@15 t4@@0 t5@@0 heap@@22 (Handle5 h@@49 r@@27 rd@@12) bx0@@48 bx1@@32 bx2@@16 bx3@@0 bx4@@0))
 :qid |unknown.0:0|
 :skolemid |844|
 :pattern ( (Requires5 t0@@73 t1@@49 t2@@30 t3@@15 t4@@0 t5@@0 heap@@22 (Handle5 h@@49 r@@27 rd@@12) bx0@@48 bx1@@32 bx2@@16 bx3@@0 bx4@@0))
)))
(assert (forall ((arg0@@206 T@U) (arg1@@101 T@U) (arg2@@59 T@U) (arg3@@37 T@U) (arg4@@26 T@U) (arg5@@16 T@U) (arg6@@14 T@U) (arg7@@3 T@U) (arg8@@2 T@U) (arg9@@0 T@U) (arg10@@0 T@U) (arg11@@0 T@U) (arg12@@0 T@U) ) (! (= (type (Reads5 arg0@@206 arg1@@101 arg2@@59 arg3@@37 arg4@@26 arg5@@16 arg6@@14 arg7@@3 arg8@@2 arg9@@0 arg10@@0 arg11@@0 arg12@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads5|
 :pattern ( (Reads5 arg0@@206 arg1@@101 arg2@@59 arg3@@37 arg4@@26 arg5@@16 arg6@@14 arg7@@3 arg8@@2 arg9@@0 arg10@@0 arg11@@0 arg12@@0))
)))
(assert (forall ((t0@@74 T@U) (t1@@50 T@U) (t2@@31 T@U) (t3@@16 T@U) (t4@@1 T@U) (t5@@1 T@U) (heap@@23 T@U) (h@@50 T@U) (r@@28 T@U) (rd@@13 T@U) (bx0@@49 T@U) (bx1@@33 T@U) (bx2@@17 T@U) (bx3@@1 T@U) (bx4@@1 T@U) (bx@@67 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@74) TyType) (= (type t1@@50) TyType)) (= (type t2@@31) TyType)) (= (type t3@@16) TyType)) (= (type t4@@1) TyType)) (= (type t5@@1) TyType)) (= (type heap@@23) (MapType0Type refType MapType1Type))) (= (type h@@50) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType BoxType))) (= (type r@@28) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType boolType))) (= (type rd@@13) (MapType5Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@49) BoxType)) (= (type bx1@@33) BoxType)) (= (type bx2@@17) BoxType)) (= (type bx3@@1) BoxType)) (= (type bx4@@1) BoxType)) (= (type bx@@67) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads5 t0@@74 t1@@50 t2@@31 t3@@16 t4@@1 t5@@1 heap@@23 (Handle5 h@@50 r@@28 rd@@13) bx0@@49 bx1@@33 bx2@@17 bx3@@1 bx4@@1) bx@@67)) (U_2_bool (MapType0Select (MapType5Select rd@@13 heap@@23 bx0@@49 bx1@@33 bx2@@17 bx3@@1 bx4@@1) bx@@67))) (=> (U_2_bool (MapType0Select (MapType5Select rd@@13 heap@@23 bx0@@49 bx1@@33 bx2@@17 bx3@@1 bx4@@1) bx@@67)) (U_2_bool (MapType0Select (Reads5 t0@@74 t1@@50 t2@@31 t3@@16 t4@@1 t5@@1 heap@@23 (Handle5 h@@50 r@@28 rd@@13) bx0@@49 bx1@@33 bx2@@17 bx3@@1 bx4@@1) bx@@67)))))
 :qid |unknown.0:0|
 :skolemid |845|
 :pattern ( (MapType0Select (Reads5 t0@@74 t1@@50 t2@@31 t3@@16 t4@@1 t5@@1 heap@@23 (Handle5 h@@50 r@@28 rd@@13) bx0@@49 bx1@@33 bx2@@17 bx3@@1 bx4@@1) bx@@67))
)))
(assert (forall ((t0@@75 T@U) (t1@@51 T@U) (t2@@32 T@U) (t3@@17 T@U) (t4@@2 T@U) (t5@@2 T@U) (h0@@24 T@U) (h1@@24 T@U) (f@@53 T@U) (bx0@@50 T@U) (bx1@@34 T@U) (bx2@@18 T@U) (bx3@@2 T@U) (bx4@@2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@75) TyType) (= (type t1@@51) TyType)) (= (type t2@@32) TyType)) (= (type t3@@17) TyType)) (= (type t4@@2) TyType)) (= (type t5@@2) TyType)) (= (type h0@@24) (MapType0Type refType MapType1Type))) (= (type h1@@24) (MapType0Type refType MapType1Type))) (= (type f@@53) HandleTypeType)) (= (type bx0@@50) BoxType)) (= (type bx1@@34) BoxType)) (= (type bx2@@18) BoxType)) (= (type bx3@@2) BoxType)) (= (type bx4@@2) BoxType)) (and (and (and ($HeapSucc h0@@24 h1@@24) (and ($IsGoodHeap h0@@24) ($IsGoodHeap h1@@24))) (and (and (and (and (and ($IsBox bx0@@50 t0@@75) ($IsBox bx1@@34 t1@@51)) ($IsBox bx2@@18 t2@@32)) ($IsBox bx3@@2 t3@@17)) ($IsBox bx4@@2 t4@@2)) ($Is f@@53 (Tclass._System.___hFunc5 t0@@75 t1@@51 t2@@32 t3@@17 t4@@2 t5@@2)))) (forall ((o@@78 T@U) (fld@@23 T@U) ) (! (let ((a@@105 (FieldTypeInv0 (type fld@@23))))
 (=> (and (and (= (type o@@78) refType) (= (type fld@@23) (FieldType a@@105))) (and (not (= o@@78 null)) (U_2_bool (MapType0Select (Reads5 t0@@75 t1@@51 t2@@32 t3@@17 t4@@2 t5@@2 h0@@24 f@@53 bx0@@50 bx1@@34 bx2@@18 bx3@@2 bx4@@2) ($Box o@@78))))) (= (MapType1Select (MapType0Select h0@@24 o@@78) fld@@23) (MapType1Select (MapType0Select h1@@24 o@@78) fld@@23))))
 :qid |unknown.0:0|
 :skolemid |846|
 :no-pattern (type o@@78)
 :no-pattern (type fld@@23)
 :no-pattern (U_2_int o@@78)
 :no-pattern (U_2_bool o@@78)
 :no-pattern (U_2_int fld@@23)
 :no-pattern (U_2_bool fld@@23)
)))) (= (Reads5 t0@@75 t1@@51 t2@@32 t3@@17 t4@@2 t5@@2 h0@@24 f@@53 bx0@@50 bx1@@34 bx2@@18 bx3@@2 bx4@@2) (Reads5 t0@@75 t1@@51 t2@@32 t3@@17 t4@@2 t5@@2 h1@@24 f@@53 bx0@@50 bx1@@34 bx2@@18 bx3@@2 bx4@@2)))
 :qid |unknown.0:0|
 :skolemid |847|
 :pattern ( ($HeapSucc h0@@24 h1@@24) (Reads5 t0@@75 t1@@51 t2@@32 t3@@17 t4@@2 t5@@2 h1@@24 f@@53 bx0@@50 bx1@@34 bx2@@18 bx3@@2 bx4@@2))
)))
(assert (forall ((t0@@76 T@U) (t1@@52 T@U) (t2@@33 T@U) (t3@@18 T@U) (t4@@3 T@U) (t5@@3 T@U) (h0@@25 T@U) (h1@@25 T@U) (f@@54 T@U) (bx0@@51 T@U) (bx1@@35 T@U) (bx2@@19 T@U) (bx3@@3 T@U) (bx4@@3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@76) TyType) (= (type t1@@52) TyType)) (= (type t2@@33) TyType)) (= (type t3@@18) TyType)) (= (type t4@@3) TyType)) (= (type t5@@3) TyType)) (= (type h0@@25) (MapType0Type refType MapType1Type))) (= (type h1@@25) (MapType0Type refType MapType1Type))) (= (type f@@54) HandleTypeType)) (= (type bx0@@51) BoxType)) (= (type bx1@@35) BoxType)) (= (type bx2@@19) BoxType)) (= (type bx3@@3) BoxType)) (= (type bx4@@3) BoxType)) (and (and (and ($HeapSucc h0@@25 h1@@25) (and ($IsGoodHeap h0@@25) ($IsGoodHeap h1@@25))) (and (and (and (and (and ($IsBox bx0@@51 t0@@76) ($IsBox bx1@@35 t1@@52)) ($IsBox bx2@@19 t2@@33)) ($IsBox bx3@@3 t3@@18)) ($IsBox bx4@@3 t4@@3)) ($Is f@@54 (Tclass._System.___hFunc5 t0@@76 t1@@52 t2@@33 t3@@18 t4@@3 t5@@3)))) (forall ((o@@79 T@U) (fld@@24 T@U) ) (! (let ((a@@106 (FieldTypeInv0 (type fld@@24))))
 (=> (and (and (= (type o@@79) refType) (= (type fld@@24) (FieldType a@@106))) (and (not (= o@@79 null)) (U_2_bool (MapType0Select (Reads5 t0@@76 t1@@52 t2@@33 t3@@18 t4@@3 t5@@3 h1@@25 f@@54 bx0@@51 bx1@@35 bx2@@19 bx3@@3 bx4@@3) ($Box o@@79))))) (= (MapType1Select (MapType0Select h0@@25 o@@79) fld@@24) (MapType1Select (MapType0Select h1@@25 o@@79) fld@@24))))
 :qid |unknown.0:0|
 :skolemid |848|
 :no-pattern (type o@@79)
 :no-pattern (type fld@@24)
 :no-pattern (U_2_int o@@79)
 :no-pattern (U_2_bool o@@79)
 :no-pattern (U_2_int fld@@24)
 :no-pattern (U_2_bool fld@@24)
)))) (= (Reads5 t0@@76 t1@@52 t2@@33 t3@@18 t4@@3 t5@@3 h0@@25 f@@54 bx0@@51 bx1@@35 bx2@@19 bx3@@3 bx4@@3) (Reads5 t0@@76 t1@@52 t2@@33 t3@@18 t4@@3 t5@@3 h1@@25 f@@54 bx0@@51 bx1@@35 bx2@@19 bx3@@3 bx4@@3)))
 :qid |unknown.0:0|
 :skolemid |849|
 :pattern ( ($HeapSucc h0@@25 h1@@25) (Reads5 t0@@76 t1@@52 t2@@33 t3@@18 t4@@3 t5@@3 h1@@25 f@@54 bx0@@51 bx1@@35 bx2@@19 bx3@@3 bx4@@3))
)))
(assert (forall ((t0@@77 T@U) (t1@@53 T@U) (t2@@34 T@U) (t3@@19 T@U) (t4@@4 T@U) (t5@@4 T@U) (h0@@26 T@U) (h1@@26 T@U) (f@@55 T@U) (bx0@@52 T@U) (bx1@@36 T@U) (bx2@@20 T@U) (bx3@@4 T@U) (bx4@@4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@77) TyType) (= (type t1@@53) TyType)) (= (type t2@@34) TyType)) (= (type t3@@19) TyType)) (= (type t4@@4) TyType)) (= (type t5@@4) TyType)) (= (type h0@@26) (MapType0Type refType MapType1Type))) (= (type h1@@26) (MapType0Type refType MapType1Type))) (= (type f@@55) HandleTypeType)) (= (type bx0@@52) BoxType)) (= (type bx1@@36) BoxType)) (= (type bx2@@20) BoxType)) (= (type bx3@@4) BoxType)) (= (type bx4@@4) BoxType)) (and (and (and ($HeapSucc h0@@26 h1@@26) (and ($IsGoodHeap h0@@26) ($IsGoodHeap h1@@26))) (and (and (and (and (and ($IsBox bx0@@52 t0@@77) ($IsBox bx1@@36 t1@@53)) ($IsBox bx2@@20 t2@@34)) ($IsBox bx3@@4 t3@@19)) ($IsBox bx4@@4 t4@@4)) ($Is f@@55 (Tclass._System.___hFunc5 t0@@77 t1@@53 t2@@34 t3@@19 t4@@4 t5@@4)))) (forall ((o@@80 T@U) (fld@@25 T@U) ) (! (let ((a@@107 (FieldTypeInv0 (type fld@@25))))
 (=> (and (and (= (type o@@80) refType) (= (type fld@@25) (FieldType a@@107))) (and (not (= o@@80 null)) (U_2_bool (MapType0Select (Reads5 t0@@77 t1@@53 t2@@34 t3@@19 t4@@4 t5@@4 h0@@26 f@@55 bx0@@52 bx1@@36 bx2@@20 bx3@@4 bx4@@4) ($Box o@@80))))) (= (MapType1Select (MapType0Select h0@@26 o@@80) fld@@25) (MapType1Select (MapType0Select h1@@26 o@@80) fld@@25))))
 :qid |unknown.0:0|
 :skolemid |850|
 :no-pattern (type o@@80)
 :no-pattern (type fld@@25)
 :no-pattern (U_2_int o@@80)
 :no-pattern (U_2_bool o@@80)
 :no-pattern (U_2_int fld@@25)
 :no-pattern (U_2_bool fld@@25)
)))) (and (=> (Requires5 t0@@77 t1@@53 t2@@34 t3@@19 t4@@4 t5@@4 h0@@26 f@@55 bx0@@52 bx1@@36 bx2@@20 bx3@@4 bx4@@4) (Requires5 t0@@77 t1@@53 t2@@34 t3@@19 t4@@4 t5@@4 h1@@26 f@@55 bx0@@52 bx1@@36 bx2@@20 bx3@@4 bx4@@4)) (=> (Requires5 t0@@77 t1@@53 t2@@34 t3@@19 t4@@4 t5@@4 h1@@26 f@@55 bx0@@52 bx1@@36 bx2@@20 bx3@@4 bx4@@4) (Requires5 t0@@77 t1@@53 t2@@34 t3@@19 t4@@4 t5@@4 h0@@26 f@@55 bx0@@52 bx1@@36 bx2@@20 bx3@@4 bx4@@4))))
 :qid |unknown.0:0|
 :skolemid |851|
 :pattern ( ($HeapSucc h0@@26 h1@@26) (Requires5 t0@@77 t1@@53 t2@@34 t3@@19 t4@@4 t5@@4 h1@@26 f@@55 bx0@@52 bx1@@36 bx2@@20 bx3@@4 bx4@@4))
)))
(assert (forall ((t0@@78 T@U) (t1@@54 T@U) (t2@@35 T@U) (t3@@20 T@U) (t4@@5 T@U) (t5@@5 T@U) (h0@@27 T@U) (h1@@27 T@U) (f@@56 T@U) (bx0@@53 T@U) (bx1@@37 T@U) (bx2@@21 T@U) (bx3@@5 T@U) (bx4@@5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@78) TyType) (= (type t1@@54) TyType)) (= (type t2@@35) TyType)) (= (type t3@@20) TyType)) (= (type t4@@5) TyType)) (= (type t5@@5) TyType)) (= (type h0@@27) (MapType0Type refType MapType1Type))) (= (type h1@@27) (MapType0Type refType MapType1Type))) (= (type f@@56) HandleTypeType)) (= (type bx0@@53) BoxType)) (= (type bx1@@37) BoxType)) (= (type bx2@@21) BoxType)) (= (type bx3@@5) BoxType)) (= (type bx4@@5) BoxType)) (and (and (and ($HeapSucc h0@@27 h1@@27) (and ($IsGoodHeap h0@@27) ($IsGoodHeap h1@@27))) (and (and (and (and (and ($IsBox bx0@@53 t0@@78) ($IsBox bx1@@37 t1@@54)) ($IsBox bx2@@21 t2@@35)) ($IsBox bx3@@5 t3@@20)) ($IsBox bx4@@5 t4@@5)) ($Is f@@56 (Tclass._System.___hFunc5 t0@@78 t1@@54 t2@@35 t3@@20 t4@@5 t5@@5)))) (forall ((o@@81 T@U) (fld@@26 T@U) ) (! (let ((a@@108 (FieldTypeInv0 (type fld@@26))))
 (=> (and (and (= (type o@@81) refType) (= (type fld@@26) (FieldType a@@108))) (and (not (= o@@81 null)) (U_2_bool (MapType0Select (Reads5 t0@@78 t1@@54 t2@@35 t3@@20 t4@@5 t5@@5 h1@@27 f@@56 bx0@@53 bx1@@37 bx2@@21 bx3@@5 bx4@@5) ($Box o@@81))))) (= (MapType1Select (MapType0Select h0@@27 o@@81) fld@@26) (MapType1Select (MapType0Select h1@@27 o@@81) fld@@26))))
 :qid |unknown.0:0|
 :skolemid |852|
 :no-pattern (type o@@81)
 :no-pattern (type fld@@26)
 :no-pattern (U_2_int o@@81)
 :no-pattern (U_2_bool o@@81)
 :no-pattern (U_2_int fld@@26)
 :no-pattern (U_2_bool fld@@26)
)))) (and (=> (Requires5 t0@@78 t1@@54 t2@@35 t3@@20 t4@@5 t5@@5 h0@@27 f@@56 bx0@@53 bx1@@37 bx2@@21 bx3@@5 bx4@@5) (Requires5 t0@@78 t1@@54 t2@@35 t3@@20 t4@@5 t5@@5 h1@@27 f@@56 bx0@@53 bx1@@37 bx2@@21 bx3@@5 bx4@@5)) (=> (Requires5 t0@@78 t1@@54 t2@@35 t3@@20 t4@@5 t5@@5 h1@@27 f@@56 bx0@@53 bx1@@37 bx2@@21 bx3@@5 bx4@@5) (Requires5 t0@@78 t1@@54 t2@@35 t3@@20 t4@@5 t5@@5 h0@@27 f@@56 bx0@@53 bx1@@37 bx2@@21 bx3@@5 bx4@@5))))
 :qid |unknown.0:0|
 :skolemid |853|
 :pattern ( ($HeapSucc h0@@27 h1@@27) (Requires5 t0@@78 t1@@54 t2@@35 t3@@20 t4@@5 t5@@5 h1@@27 f@@56 bx0@@53 bx1@@37 bx2@@21 bx3@@5 bx4@@5))
)))
(assert (forall ((t0@@79 T@U) (t1@@55 T@U) (t2@@36 T@U) (t3@@21 T@U) (t4@@6 T@U) (t5@@6 T@U) (h0@@28 T@U) (h1@@28 T@U) (f@@57 T@U) (bx0@@54 T@U) (bx1@@38 T@U) (bx2@@22 T@U) (bx3@@6 T@U) (bx4@@6 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@79) TyType) (= (type t1@@55) TyType)) (= (type t2@@36) TyType)) (= (type t3@@21) TyType)) (= (type t4@@6) TyType)) (= (type t5@@6) TyType)) (= (type h0@@28) (MapType0Type refType MapType1Type))) (= (type h1@@28) (MapType0Type refType MapType1Type))) (= (type f@@57) HandleTypeType)) (= (type bx0@@54) BoxType)) (= (type bx1@@38) BoxType)) (= (type bx2@@22) BoxType)) (= (type bx3@@6) BoxType)) (= (type bx4@@6) BoxType)) (and (and (and ($HeapSucc h0@@28 h1@@28) (and ($IsGoodHeap h0@@28) ($IsGoodHeap h1@@28))) (and (and (and (and (and ($IsBox bx0@@54 t0@@79) ($IsBox bx1@@38 t1@@55)) ($IsBox bx2@@22 t2@@36)) ($IsBox bx3@@6 t3@@21)) ($IsBox bx4@@6 t4@@6)) ($Is f@@57 (Tclass._System.___hFunc5 t0@@79 t1@@55 t2@@36 t3@@21 t4@@6 t5@@6)))) (forall ((o@@82 T@U) (fld@@27 T@U) ) (! (let ((a@@109 (FieldTypeInv0 (type fld@@27))))
 (=> (and (and (= (type o@@82) refType) (= (type fld@@27) (FieldType a@@109))) (and (not (= o@@82 null)) (U_2_bool (MapType0Select (Reads5 t0@@79 t1@@55 t2@@36 t3@@21 t4@@6 t5@@6 h0@@28 f@@57 bx0@@54 bx1@@38 bx2@@22 bx3@@6 bx4@@6) ($Box o@@82))))) (= (MapType1Select (MapType0Select h0@@28 o@@82) fld@@27) (MapType1Select (MapType0Select h1@@28 o@@82) fld@@27))))
 :qid |unknown.0:0|
 :skolemid |854|
 :no-pattern (type o@@82)
 :no-pattern (type fld@@27)
 :no-pattern (U_2_int o@@82)
 :no-pattern (U_2_bool o@@82)
 :no-pattern (U_2_int fld@@27)
 :no-pattern (U_2_bool fld@@27)
)))) (= (Apply5 t0@@79 t1@@55 t2@@36 t3@@21 t4@@6 t5@@6 h0@@28 f@@57 bx0@@54 bx1@@38 bx2@@22 bx3@@6 bx4@@6) (Apply5 t0@@79 t1@@55 t2@@36 t3@@21 t4@@6 t5@@6 h1@@28 f@@57 bx0@@54 bx1@@38 bx2@@22 bx3@@6 bx4@@6)))
 :qid |unknown.0:0|
 :skolemid |855|
 :pattern ( ($HeapSucc h0@@28 h1@@28) (Apply5 t0@@79 t1@@55 t2@@36 t3@@21 t4@@6 t5@@6 h1@@28 f@@57 bx0@@54 bx1@@38 bx2@@22 bx3@@6 bx4@@6))
)))
(assert (forall ((t0@@80 T@U) (t1@@56 T@U) (t2@@37 T@U) (t3@@22 T@U) (t4@@7 T@U) (t5@@7 T@U) (h0@@29 T@U) (h1@@29 T@U) (f@@58 T@U) (bx0@@55 T@U) (bx1@@39 T@U) (bx2@@23 T@U) (bx3@@7 T@U) (bx4@@7 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@80) TyType) (= (type t1@@56) TyType)) (= (type t2@@37) TyType)) (= (type t3@@22) TyType)) (= (type t4@@7) TyType)) (= (type t5@@7) TyType)) (= (type h0@@29) (MapType0Type refType MapType1Type))) (= (type h1@@29) (MapType0Type refType MapType1Type))) (= (type f@@58) HandleTypeType)) (= (type bx0@@55) BoxType)) (= (type bx1@@39) BoxType)) (= (type bx2@@23) BoxType)) (= (type bx3@@7) BoxType)) (= (type bx4@@7) BoxType)) (and (and (and ($HeapSucc h0@@29 h1@@29) (and ($IsGoodHeap h0@@29) ($IsGoodHeap h1@@29))) (and (and (and (and (and ($IsBox bx0@@55 t0@@80) ($IsBox bx1@@39 t1@@56)) ($IsBox bx2@@23 t2@@37)) ($IsBox bx3@@7 t3@@22)) ($IsBox bx4@@7 t4@@7)) ($Is f@@58 (Tclass._System.___hFunc5 t0@@80 t1@@56 t2@@37 t3@@22 t4@@7 t5@@7)))) (forall ((o@@83 T@U) (fld@@28 T@U) ) (! (let ((a@@110 (FieldTypeInv0 (type fld@@28))))
 (=> (and (and (= (type o@@83) refType) (= (type fld@@28) (FieldType a@@110))) (and (not (= o@@83 null)) (U_2_bool (MapType0Select (Reads5 t0@@80 t1@@56 t2@@37 t3@@22 t4@@7 t5@@7 h1@@29 f@@58 bx0@@55 bx1@@39 bx2@@23 bx3@@7 bx4@@7) ($Box o@@83))))) (= (MapType1Select (MapType0Select h0@@29 o@@83) fld@@28) (MapType1Select (MapType0Select h1@@29 o@@83) fld@@28))))
 :qid |unknown.0:0|
 :skolemid |856|
 :no-pattern (type o@@83)
 :no-pattern (type fld@@28)
 :no-pattern (U_2_int o@@83)
 :no-pattern (U_2_bool o@@83)
 :no-pattern (U_2_int fld@@28)
 :no-pattern (U_2_bool fld@@28)
)))) (= (Apply5 t0@@80 t1@@56 t2@@37 t3@@22 t4@@7 t5@@7 h0@@29 f@@58 bx0@@55 bx1@@39 bx2@@23 bx3@@7 bx4@@7) (Apply5 t0@@80 t1@@56 t2@@37 t3@@22 t4@@7 t5@@7 h1@@29 f@@58 bx0@@55 bx1@@39 bx2@@23 bx3@@7 bx4@@7)))
 :qid |unknown.0:0|
 :skolemid |857|
 :pattern ( ($HeapSucc h0@@29 h1@@29) (Apply5 t0@@80 t1@@56 t2@@37 t3@@22 t4@@7 t5@@7 h1@@29 f@@58 bx0@@55 bx1@@39 bx2@@23 bx3@@7 bx4@@7))
)))
(assert (forall ((t0@@81 T@U) (t1@@57 T@U) (t2@@38 T@U) (t3@@23 T@U) (t4@@8 T@U) (t5@@8 T@U) (heap@@24 T@U) (f@@59 T@U) (bx0@@56 T@U) (bx1@@40 T@U) (bx2@@24 T@U) (bx3@@8 T@U) (bx4@@8 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@81) TyType) (= (type t1@@57) TyType)) (= (type t2@@38) TyType)) (= (type t3@@23) TyType)) (= (type t4@@8) TyType)) (= (type t5@@8) TyType)) (= (type heap@@24) (MapType0Type refType MapType1Type))) (= (type f@@59) HandleTypeType)) (= (type bx0@@56) BoxType)) (= (type bx1@@40) BoxType)) (= (type bx2@@24) BoxType)) (= (type bx3@@8) BoxType)) (= (type bx4@@8) BoxType)) (and ($IsGoodHeap heap@@24) (and (and (and (and (and ($IsBox bx0@@56 t0@@81) ($IsBox bx1@@40 t1@@57)) ($IsBox bx2@@24 t2@@38)) ($IsBox bx3@@8 t3@@23)) ($IsBox bx4@@8 t4@@8)) ($Is f@@59 (Tclass._System.___hFunc5 t0@@81 t1@@57 t2@@38 t3@@23 t4@@8 t5@@8))))) (and (=> (|Set#Equal| (Reads5 t0@@81 t1@@57 t2@@38 t3@@23 t4@@8 t5@@8 $OneHeap f@@59 bx0@@56 bx1@@40 bx2@@24 bx3@@8 bx4@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads5 t0@@81 t1@@57 t2@@38 t3@@23 t4@@8 t5@@8 heap@@24 f@@59 bx0@@56 bx1@@40 bx2@@24 bx3@@8 bx4@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads5 t0@@81 t1@@57 t2@@38 t3@@23 t4@@8 t5@@8 heap@@24 f@@59 bx0@@56 bx1@@40 bx2@@24 bx3@@8 bx4@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads5 t0@@81 t1@@57 t2@@38 t3@@23 t4@@8 t5@@8 $OneHeap f@@59 bx0@@56 bx1@@40 bx2@@24 bx3@@8 bx4@@8) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |858|
 :pattern ( (Reads5 t0@@81 t1@@57 t2@@38 t3@@23 t4@@8 t5@@8 $OneHeap f@@59 bx0@@56 bx1@@40 bx2@@24 bx3@@8 bx4@@8) ($IsGoodHeap heap@@24))
 :pattern ( (Reads5 t0@@81 t1@@57 t2@@38 t3@@23 t4@@8 t5@@8 heap@@24 f@@59 bx0@@56 bx1@@40 bx2@@24 bx3@@8 bx4@@8))
)))
(assert (forall ((t0@@82 T@U) (t1@@58 T@U) (t2@@39 T@U) (t3@@24 T@U) (t4@@9 T@U) (t5@@9 T@U) (heap@@25 T@U) (f@@60 T@U) (bx0@@57 T@U) (bx1@@41 T@U) (bx2@@25 T@U) (bx3@@9 T@U) (bx4@@9 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type t0@@82) TyType) (= (type t1@@58) TyType)) (= (type t2@@39) TyType)) (= (type t3@@24) TyType)) (= (type t4@@9) TyType)) (= (type t5@@9) TyType)) (= (type heap@@25) (MapType0Type refType MapType1Type))) (= (type f@@60) HandleTypeType)) (= (type bx0@@57) BoxType)) (= (type bx1@@41) BoxType)) (= (type bx2@@25) BoxType)) (= (type bx3@@9) BoxType)) (= (type bx4@@9) BoxType)) (and (and ($IsGoodHeap heap@@25) (and (and (and (and (and ($IsBox bx0@@57 t0@@82) ($IsBox bx1@@41 t1@@58)) ($IsBox bx2@@25 t2@@39)) ($IsBox bx3@@9 t3@@24)) ($IsBox bx4@@9 t4@@9)) ($Is f@@60 (Tclass._System.___hFunc5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9)))) (|Set#Equal| (Reads5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9 $OneHeap f@@60 bx0@@57 bx1@@41 bx2@@25 bx3@@9 bx4@@9) (|Set#Empty| BoxType)))) (and (=> (Requires5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9 $OneHeap f@@60 bx0@@57 bx1@@41 bx2@@25 bx3@@9 bx4@@9) (Requires5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9 heap@@25 f@@60 bx0@@57 bx1@@41 bx2@@25 bx3@@9 bx4@@9)) (=> (Requires5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9 heap@@25 f@@60 bx0@@57 bx1@@41 bx2@@25 bx3@@9 bx4@@9) (Requires5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9 $OneHeap f@@60 bx0@@57 bx1@@41 bx2@@25 bx3@@9 bx4@@9))))
 :qid |unknown.0:0|
 :skolemid |859|
 :pattern ( (Requires5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9 $OneHeap f@@60 bx0@@57 bx1@@41 bx2@@25 bx3@@9 bx4@@9) ($IsGoodHeap heap@@25))
 :pattern ( (Requires5 t0@@82 t1@@58 t2@@39 t3@@24 t4@@9 t5@@9 heap@@25 f@@60 bx0@@57 bx1@@41 bx2@@25 bx3@@9 bx4@@9))
)))
(assert (forall ((f@@61 T@U) (t0@@83 T@U) (t1@@59 T@U) (t2@@40 T@U) (t3@@25 T@U) (t4@@10 T@U) (t5@@10 T@U) ) (!  (=> (and (and (and (and (and (and (= (type f@@61) HandleTypeType) (= (type t0@@83) TyType)) (= (type t1@@59) TyType)) (= (type t2@@40) TyType)) (= (type t3@@25) TyType)) (= (type t4@@10) TyType)) (= (type t5@@10) TyType)) (and (=> ($Is f@@61 (Tclass._System.___hFunc5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10)) (forall ((h@@51 T@U) (bx0@@58 T@U) (bx1@@42 T@U) (bx2@@26 T@U) (bx3@@10 T@U) (bx4@@10 T@U) ) (!  (=> (and (and (and (and (and (and (= (type h@@51) (MapType0Type refType MapType1Type)) (= (type bx0@@58) BoxType)) (= (type bx1@@42) BoxType)) (= (type bx2@@26) BoxType)) (= (type bx3@@10) BoxType)) (= (type bx4@@10) BoxType)) (and (and ($IsGoodHeap h@@51) (and (and (and (and ($IsBox bx0@@58 t0@@83) ($IsBox bx1@@42 t1@@59)) ($IsBox bx2@@26 t2@@40)) ($IsBox bx3@@10 t3@@25)) ($IsBox bx4@@10 t4@@10))) (Requires5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10 h@@51 f@@61 bx0@@58 bx1@@42 bx2@@26 bx3@@10 bx4@@10))) ($IsBox (Apply5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10 h@@51 f@@61 bx0@@58 bx1@@42 bx2@@26 bx3@@10 bx4@@10) t5@@10))
 :qid |DafnyPre.515:12|
 :skolemid |860|
 :pattern ( (Apply5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10 h@@51 f@@61 bx0@@58 bx1@@42 bx2@@26 bx3@@10 bx4@@10))
))) (=> (forall ((h@@52 T@U) (bx0@@59 T@U) (bx1@@43 T@U) (bx2@@27 T@U) (bx3@@11 T@U) (bx4@@11 T@U) ) (!  (=> (and (and (and (and (and (and (= (type h@@52) (MapType0Type refType MapType1Type)) (= (type bx0@@59) BoxType)) (= (type bx1@@43) BoxType)) (= (type bx2@@27) BoxType)) (= (type bx3@@11) BoxType)) (= (type bx4@@11) BoxType)) (and (and ($IsGoodHeap h@@52) (and (and (and (and ($IsBox bx0@@59 t0@@83) ($IsBox bx1@@43 t1@@59)) ($IsBox bx2@@27 t2@@40)) ($IsBox bx3@@11 t3@@25)) ($IsBox bx4@@11 t4@@10))) (Requires5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10 h@@52 f@@61 bx0@@59 bx1@@43 bx2@@27 bx3@@11 bx4@@11))) ($IsBox (Apply5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10 h@@52 f@@61 bx0@@59 bx1@@43 bx2@@27 bx3@@11 bx4@@11) t5@@10))
 :qid |DafnyPre.515:12|
 :skolemid |860|
 :pattern ( (Apply5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10 h@@52 f@@61 bx0@@59 bx1@@43 bx2@@27 bx3@@11 bx4@@11))
)) ($Is f@@61 (Tclass._System.___hFunc5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10)))))
 :qid |unknown.0:0|
 :skolemid |861|
 :pattern ( ($Is f@@61 (Tclass._System.___hFunc5 t0@@83 t1@@59 t2@@40 t3@@25 t4@@10 t5@@10)))
)))
(assert (forall ((f@@62 T@U) (t0@@84 T@U) (t1@@60 T@U) (t2@@41 T@U) (t3@@26 T@U) (t4@@11 T@U) (t5@@11 T@U) (u0@@3 T@U) (u1@@2 T@U) (u2@@1 T@U) (u3@@0 T@U) (u4 T@U) (u5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type f@@62) HandleTypeType) (= (type t0@@84) TyType)) (= (type t1@@60) TyType)) (= (type t2@@41) TyType)) (= (type t3@@26) TyType)) (= (type t4@@11) TyType)) (= (type t5@@11) TyType)) (= (type u0@@3) TyType)) (= (type u1@@2) TyType)) (= (type u2@@1) TyType)) (= (type u3@@0) TyType)) (= (type u4) TyType)) (= (type u5) TyType)) (and (and (and (and (and (and ($Is f@@62 (Tclass._System.___hFunc5 t0@@84 t1@@60 t2@@41 t3@@26 t4@@11 t5@@11)) (forall ((bx@@68 T@U) ) (!  (=> (and (= (type bx@@68) BoxType) ($IsBox bx@@68 u0@@3)) ($IsBox bx@@68 t0@@84))
 :qid |unknown.0:0|
 :skolemid |862|
 :pattern ( ($IsBox bx@@68 u0@@3))
 :pattern ( ($IsBox bx@@68 t0@@84))
))) (forall ((bx@@69 T@U) ) (!  (=> (and (= (type bx@@69) BoxType) ($IsBox bx@@69 u1@@2)) ($IsBox bx@@69 t1@@60))
 :qid |unknown.0:0|
 :skolemid |863|
 :pattern ( ($IsBox bx@@69 u1@@2))
 :pattern ( ($IsBox bx@@69 t1@@60))
))) (forall ((bx@@70 T@U) ) (!  (=> (and (= (type bx@@70) BoxType) ($IsBox bx@@70 u2@@1)) ($IsBox bx@@70 t2@@41))
 :qid |unknown.0:0|
 :skolemid |864|
 :pattern ( ($IsBox bx@@70 u2@@1))
 :pattern ( ($IsBox bx@@70 t2@@41))
))) (forall ((bx@@71 T@U) ) (!  (=> (and (= (type bx@@71) BoxType) ($IsBox bx@@71 u3@@0)) ($IsBox bx@@71 t3@@26))
 :qid |unknown.0:0|
 :skolemid |865|
 :pattern ( ($IsBox bx@@71 u3@@0))
 :pattern ( ($IsBox bx@@71 t3@@26))
))) (forall ((bx@@72 T@U) ) (!  (=> (and (= (type bx@@72) BoxType) ($IsBox bx@@72 u4)) ($IsBox bx@@72 t4@@11))
 :qid |unknown.0:0|
 :skolemid |866|
 :pattern ( ($IsBox bx@@72 u4))
 :pattern ( ($IsBox bx@@72 t4@@11))
))) (forall ((bx@@73 T@U) ) (!  (=> (and (= (type bx@@73) BoxType) ($IsBox bx@@73 t5@@11)) ($IsBox bx@@73 u5))
 :qid |unknown.0:0|
 :skolemid |867|
 :pattern ( ($IsBox bx@@73 t5@@11))
 :pattern ( ($IsBox bx@@73 u5))
)))) ($Is f@@62 (Tclass._System.___hFunc5 u0@@3 u1@@2 u2@@1 u3@@0 u4 u5)))
 :qid |unknown.0:0|
 :skolemid |868|
 :pattern ( ($Is f@@62 (Tclass._System.___hFunc5 t0@@84 t1@@60 t2@@41 t3@@26 t4@@11 t5@@11)) ($Is f@@62 (Tclass._System.___hFunc5 u0@@3 u1@@2 u2@@1 u3@@0 u4 u5)))
)))
(assert (forall ((f@@63 T@U) (t0@@85 T@U) (t1@@61 T@U) (t2@@42 T@U) (t3@@27 T@U) (t4@@12 T@U) (t5@@12 T@U) (h@@53 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type f@@63) HandleTypeType) (= (type t0@@85) TyType)) (= (type t1@@61) TyType)) (= (type t2@@42) TyType)) (= (type t3@@27) TyType)) (= (type t4@@12) TyType)) (= (type t5@@12) TyType)) (= (type h@@53) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@53)) (and (=> ($IsAlloc f@@63 (Tclass._System.___hFunc5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12) h@@53) (forall ((bx0@@60 T@U) (bx1@@44 T@U) (bx2@@28 T@U) (bx3@@12 T@U) (bx4@@12 T@U) ) (!  (=> (and (and (and (and (= (type bx0@@60) BoxType) (= (type bx1@@44) BoxType)) (= (type bx2@@28) BoxType)) (= (type bx3@@12) BoxType)) (= (type bx4@@12) BoxType)) (=> (and (and (and (and (and (and ($IsBox bx0@@60 t0@@85) ($IsAllocBox bx0@@60 t0@@85 h@@53)) (and ($IsBox bx1@@44 t1@@61) ($IsAllocBox bx1@@44 t1@@61 h@@53))) (and ($IsBox bx2@@28 t2@@42) ($IsAllocBox bx2@@28 t2@@42 h@@53))) (and ($IsBox bx3@@12 t3@@27) ($IsAllocBox bx3@@12 t3@@27 h@@53))) (and ($IsBox bx4@@12 t4@@12) ($IsAllocBox bx4@@12 t4@@12 h@@53))) (Requires5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@60 bx1@@44 bx2@@28 bx3@@12 bx4@@12)) (forall ((r@@29 T@U) ) (!  (=> (= (type r@@29) refType) (=> (and (not (= r@@29 null)) (U_2_bool (MapType0Select (Reads5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@60 bx1@@44 bx2@@28 bx3@@12 bx4@@12) ($Box r@@29)))) (U_2_bool (MapType1Select (MapType0Select h@@53 r@@29) alloc))))
 :qid |unknown.0:0|
 :skolemid |869|
 :pattern ( (MapType0Select (Reads5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@60 bx1@@44 bx2@@28 bx3@@12 bx4@@12) ($Box r@@29)))
))))
 :qid |unknown.0:0|
 :skolemid |870|
 :pattern ( (Apply5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@60 bx1@@44 bx2@@28 bx3@@12 bx4@@12))
 :pattern ( (Reads5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@60 bx1@@44 bx2@@28 bx3@@12 bx4@@12))
))) (=> (forall ((bx0@@61 T@U) (bx1@@45 T@U) (bx2@@29 T@U) (bx3@@13 T@U) (bx4@@13 T@U) ) (!  (=> (and (and (and (and (= (type bx0@@61) BoxType) (= (type bx1@@45) BoxType)) (= (type bx2@@29) BoxType)) (= (type bx3@@13) BoxType)) (= (type bx4@@13) BoxType)) (=> (and (and (and (and (and (and ($IsBox bx0@@61 t0@@85) ($IsAllocBox bx0@@61 t0@@85 h@@53)) (and ($IsBox bx1@@45 t1@@61) ($IsAllocBox bx1@@45 t1@@61 h@@53))) (and ($IsBox bx2@@29 t2@@42) ($IsAllocBox bx2@@29 t2@@42 h@@53))) (and ($IsBox bx3@@13 t3@@27) ($IsAllocBox bx3@@13 t3@@27 h@@53))) (and ($IsBox bx4@@13 t4@@12) ($IsAllocBox bx4@@13 t4@@12 h@@53))) (Requires5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@61 bx1@@45 bx2@@29 bx3@@13 bx4@@13)) (forall ((r@@30 T@U) ) (!  (=> (= (type r@@30) refType) (=> (and (not (= r@@30 null)) (U_2_bool (MapType0Select (Reads5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@61 bx1@@45 bx2@@29 bx3@@13 bx4@@13) ($Box r@@30)))) (U_2_bool (MapType1Select (MapType0Select h@@53 r@@30) alloc))))
 :qid |unknown.0:0|
 :skolemid |869|
 :pattern ( (MapType0Select (Reads5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@61 bx1@@45 bx2@@29 bx3@@13 bx4@@13) ($Box r@@30)))
))))
 :qid |unknown.0:0|
 :skolemid |870|
 :pattern ( (Apply5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@61 bx1@@45 bx2@@29 bx3@@13 bx4@@13))
 :pattern ( (Reads5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12 h@@53 f@@63 bx0@@61 bx1@@45 bx2@@29 bx3@@13 bx4@@13))
)) ($IsAlloc f@@63 (Tclass._System.___hFunc5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12) h@@53))))
 :qid |unknown.0:0|
 :skolemid |871|
 :pattern ( ($IsAlloc f@@63 (Tclass._System.___hFunc5 t0@@85 t1@@61 t2@@42 t3@@27 t4@@12 t5@@12) h@@53))
)))
(assert (forall ((f@@64 T@U) (t0@@86 T@U) (t1@@62 T@U) (t2@@43 T@U) (t3@@28 T@U) (t4@@13 T@U) (t5@@13 T@U) (h@@54 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type f@@64) HandleTypeType) (= (type t0@@86) TyType)) (= (type t1@@62) TyType)) (= (type t2@@43) TyType)) (= (type t3@@28) TyType)) (= (type t4@@13) TyType)) (= (type t5@@13) TyType)) (= (type h@@54) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@54) ($IsAlloc f@@64 (Tclass._System.___hFunc5 t0@@86 t1@@62 t2@@43 t3@@28 t4@@13 t5@@13) h@@54))) (forall ((bx0@@62 T@U) (bx1@@46 T@U) (bx2@@30 T@U) (bx3@@14 T@U) (bx4@@14 T@U) ) (!  (=> (and (and (and (and (= (type bx0@@62) BoxType) (= (type bx1@@46) BoxType)) (= (type bx2@@30) BoxType)) (= (type bx3@@14) BoxType)) (= (type bx4@@14) BoxType)) (=> (and (and (and (and (and ($IsAllocBox bx0@@62 t0@@86 h@@54) ($IsAllocBox bx1@@46 t1@@62 h@@54)) ($IsAllocBox bx2@@30 t2@@43 h@@54)) ($IsAllocBox bx3@@14 t3@@28 h@@54)) ($IsAllocBox bx4@@14 t4@@13 h@@54)) (Requires5 t0@@86 t1@@62 t2@@43 t3@@28 t4@@13 t5@@13 h@@54 f@@64 bx0@@62 bx1@@46 bx2@@30 bx3@@14 bx4@@14)) ($IsAllocBox (Apply5 t0@@86 t1@@62 t2@@43 t3@@28 t4@@13 t5@@13 h@@54 f@@64 bx0@@62 bx1@@46 bx2@@30 bx3@@14 bx4@@14) t5@@13 h@@54)))
 :qid |unknown.0:0|
 :skolemid |872|
 :pattern ( (Apply5 t0@@86 t1@@62 t2@@43 t3@@28 t4@@13 t5@@13 h@@54 f@@64 bx0@@62 bx1@@46 bx2@@30 bx3@@14 bx4@@14))
)))
 :qid |unknown.0:0|
 :skolemid |873|
 :pattern ( ($IsAlloc f@@64 (Tclass._System.___hFunc5 t0@@86 t1@@62 t2@@43 t3@@28 t4@@13 t5@@13) h@@54))
)))
(assert (forall ((arg0@@207 T@U) (arg1@@102 T@U) (arg2@@60 T@U) (arg3@@38 T@U) (arg4@@27 T@U) (arg5@@17 T@U) ) (! (= (type (Tclass._System.___hPartialFunc5 arg0@@207 arg1@@102 arg2@@60 arg3@@38 arg4@@27 arg5@@17)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc5|
 :pattern ( (Tclass._System.___hPartialFunc5 arg0@@207 arg1@@102 arg2@@60 arg3@@38 arg4@@27 arg5@@17))
)))
(assert (forall ((|#$T0@@64| T@U) (|#$T1@@48| T@U) (|#$T2@@29| T@U) (|#$T3@@7| T@U) (|#$T4@@7| T@U) (|#$R@@77| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@64|) TyType) (= (type |#$T1@@48|) TyType)) (= (type |#$T2@@29|) TyType)) (= (type |#$T3@@7|) TyType)) (= (type |#$T4@@7|) TyType)) (= (type |#$R@@77|) TyType)) (= (Tag (Tclass._System.___hPartialFunc5 |#$T0@@64| |#$T1@@48| |#$T2@@29| |#$T3@@7| |#$T4@@7| |#$R@@77|)) Tagclass._System.___hPartialFunc5))
 :qid |unknown.0:0|
 :skolemid |874|
 :pattern ( (Tclass._System.___hPartialFunc5 |#$T0@@64| |#$T1@@48| |#$T2@@29| |#$T3@@7| |#$T4@@7| |#$R@@77|))
)))
(assert (forall ((arg0@@208 T@U) ) (! (= (type (Tclass._System.___hPartialFunc5_0 arg0@@208)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc5_0|
 :pattern ( (Tclass._System.___hPartialFunc5_0 arg0@@208))
)))
(assert (forall ((|#$T0@@65| T@U) (|#$T1@@49| T@U) (|#$T2@@30| T@U) (|#$T3@@8| T@U) (|#$T4@@8| T@U) (|#$R@@78| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@65|) TyType) (= (type |#$T1@@49|) TyType)) (= (type |#$T2@@30|) TyType)) (= (type |#$T3@@8|) TyType)) (= (type |#$T4@@8|) TyType)) (= (type |#$R@@78|) TyType)) (= (Tclass._System.___hPartialFunc5_0 (Tclass._System.___hPartialFunc5 |#$T0@@65| |#$T1@@49| |#$T2@@30| |#$T3@@8| |#$T4@@8| |#$R@@78|)) |#$T0@@65|))
 :qid |unknown.0:0|
 :skolemid |875|
 :pattern ( (Tclass._System.___hPartialFunc5 |#$T0@@65| |#$T1@@49| |#$T2@@30| |#$T3@@8| |#$T4@@8| |#$R@@78|))
)))
(assert (forall ((arg0@@209 T@U) ) (! (= (type (Tclass._System.___hPartialFunc5_1 arg0@@209)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc5_1|
 :pattern ( (Tclass._System.___hPartialFunc5_1 arg0@@209))
)))
(assert (forall ((|#$T0@@66| T@U) (|#$T1@@50| T@U) (|#$T2@@31| T@U) (|#$T3@@9| T@U) (|#$T4@@9| T@U) (|#$R@@79| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@66|) TyType) (= (type |#$T1@@50|) TyType)) (= (type |#$T2@@31|) TyType)) (= (type |#$T3@@9|) TyType)) (= (type |#$T4@@9|) TyType)) (= (type |#$R@@79|) TyType)) (= (Tclass._System.___hPartialFunc5_1 (Tclass._System.___hPartialFunc5 |#$T0@@66| |#$T1@@50| |#$T2@@31| |#$T3@@9| |#$T4@@9| |#$R@@79|)) |#$T1@@50|))
 :qid |unknown.0:0|
 :skolemid |876|
 :pattern ( (Tclass._System.___hPartialFunc5 |#$T0@@66| |#$T1@@50| |#$T2@@31| |#$T3@@9| |#$T4@@9| |#$R@@79|))
)))
(assert (forall ((arg0@@210 T@U) ) (! (= (type (Tclass._System.___hPartialFunc5_2 arg0@@210)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc5_2|
 :pattern ( (Tclass._System.___hPartialFunc5_2 arg0@@210))
)))
(assert (forall ((|#$T0@@67| T@U) (|#$T1@@51| T@U) (|#$T2@@32| T@U) (|#$T3@@10| T@U) (|#$T4@@10| T@U) (|#$R@@80| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@67|) TyType) (= (type |#$T1@@51|) TyType)) (= (type |#$T2@@32|) TyType)) (= (type |#$T3@@10|) TyType)) (= (type |#$T4@@10|) TyType)) (= (type |#$R@@80|) TyType)) (= (Tclass._System.___hPartialFunc5_2 (Tclass._System.___hPartialFunc5 |#$T0@@67| |#$T1@@51| |#$T2@@32| |#$T3@@10| |#$T4@@10| |#$R@@80|)) |#$T2@@32|))
 :qid |unknown.0:0|
 :skolemid |877|
 :pattern ( (Tclass._System.___hPartialFunc5 |#$T0@@67| |#$T1@@51| |#$T2@@32| |#$T3@@10| |#$T4@@10| |#$R@@80|))
)))
(assert (forall ((arg0@@211 T@U) ) (! (= (type (Tclass._System.___hPartialFunc5_3 arg0@@211)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc5_3|
 :pattern ( (Tclass._System.___hPartialFunc5_3 arg0@@211))
)))
(assert (forall ((|#$T0@@68| T@U) (|#$T1@@52| T@U) (|#$T2@@33| T@U) (|#$T3@@11| T@U) (|#$T4@@11| T@U) (|#$R@@81| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@68|) TyType) (= (type |#$T1@@52|) TyType)) (= (type |#$T2@@33|) TyType)) (= (type |#$T3@@11|) TyType)) (= (type |#$T4@@11|) TyType)) (= (type |#$R@@81|) TyType)) (= (Tclass._System.___hPartialFunc5_3 (Tclass._System.___hPartialFunc5 |#$T0@@68| |#$T1@@52| |#$T2@@33| |#$T3@@11| |#$T4@@11| |#$R@@81|)) |#$T3@@11|))
 :qid |unknown.0:0|
 :skolemid |878|
 :pattern ( (Tclass._System.___hPartialFunc5 |#$T0@@68| |#$T1@@52| |#$T2@@33| |#$T3@@11| |#$T4@@11| |#$R@@81|))
)))
(assert (forall ((arg0@@212 T@U) ) (! (= (type (Tclass._System.___hPartialFunc5_4 arg0@@212)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc5_4|
 :pattern ( (Tclass._System.___hPartialFunc5_4 arg0@@212))
)))
(assert (forall ((|#$T0@@69| T@U) (|#$T1@@53| T@U) (|#$T2@@34| T@U) (|#$T3@@12| T@U) (|#$T4@@12| T@U) (|#$R@@82| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@69|) TyType) (= (type |#$T1@@53|) TyType)) (= (type |#$T2@@34|) TyType)) (= (type |#$T3@@12|) TyType)) (= (type |#$T4@@12|) TyType)) (= (type |#$R@@82|) TyType)) (= (Tclass._System.___hPartialFunc5_4 (Tclass._System.___hPartialFunc5 |#$T0@@69| |#$T1@@53| |#$T2@@34| |#$T3@@12| |#$T4@@12| |#$R@@82|)) |#$T4@@12|))
 :qid |unknown.0:0|
 :skolemid |879|
 :pattern ( (Tclass._System.___hPartialFunc5 |#$T0@@69| |#$T1@@53| |#$T2@@34| |#$T3@@12| |#$T4@@12| |#$R@@82|))
)))
(assert (forall ((arg0@@213 T@U) ) (! (= (type (Tclass._System.___hPartialFunc5_5 arg0@@213)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc5_5|
 :pattern ( (Tclass._System.___hPartialFunc5_5 arg0@@213))
)))
(assert (forall ((|#$T0@@70| T@U) (|#$T1@@54| T@U) (|#$T2@@35| T@U) (|#$T3@@13| T@U) (|#$T4@@13| T@U) (|#$R@@83| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@70|) TyType) (= (type |#$T1@@54|) TyType)) (= (type |#$T2@@35|) TyType)) (= (type |#$T3@@13|) TyType)) (= (type |#$T4@@13|) TyType)) (= (type |#$R@@83|) TyType)) (= (Tclass._System.___hPartialFunc5_5 (Tclass._System.___hPartialFunc5 |#$T0@@70| |#$T1@@54| |#$T2@@35| |#$T3@@13| |#$T4@@13| |#$R@@83|)) |#$R@@83|))
 :qid |unknown.0:0|
 :skolemid |880|
 :pattern ( (Tclass._System.___hPartialFunc5 |#$T0@@70| |#$T1@@54| |#$T2@@35| |#$T3@@13| |#$T4@@13| |#$R@@83|))
)))
(assert (forall ((|#$T0@@71| T@U) (|#$T1@@55| T@U) (|#$T2@@36| T@U) (|#$T3@@14| T@U) (|#$T4@@14| T@U) (|#$R@@84| T@U) (bx@@74 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type |#$T0@@71|) TyType) (= (type |#$T1@@55|) TyType)) (= (type |#$T2@@36|) TyType)) (= (type |#$T3@@14|) TyType)) (= (type |#$T4@@14|) TyType)) (= (type |#$R@@84|) TyType)) (= (type bx@@74) BoxType)) ($IsBox bx@@74 (Tclass._System.___hPartialFunc5 |#$T0@@71| |#$T1@@55| |#$T2@@36| |#$T3@@14| |#$T4@@14| |#$R@@84|))) (and (= ($Box ($Unbox HandleTypeType bx@@74)) bx@@74) ($Is ($Unbox HandleTypeType bx@@74) (Tclass._System.___hPartialFunc5 |#$T0@@71| |#$T1@@55| |#$T2@@36| |#$T3@@14| |#$T4@@14| |#$R@@84|))))
 :qid |unknown.0:0|
 :skolemid |881|
 :pattern ( ($IsBox bx@@74 (Tclass._System.___hPartialFunc5 |#$T0@@71| |#$T1@@55| |#$T2@@36| |#$T3@@14| |#$T4@@14| |#$R@@84|)))
)))
(assert (forall ((|#$T0@@72| T@U) (|#$T1@@56| T@U) (|#$T2@@37| T@U) (|#$T3@@15| T@U) (|#$T4@@15| T@U) (|#$R@@85| T@U) (|f#0@@15| T@U) ) (!  (=> (and (and (and (and (and (and (= (type |#$T0@@72|) TyType) (= (type |#$T1@@56|) TyType)) (= (type |#$T2@@37|) TyType)) (= (type |#$T3@@15|) TyType)) (= (type |#$T4@@15|) TyType)) (= (type |#$R@@85|) TyType)) (= (type |f#0@@15|) HandleTypeType)) (and (=> ($Is |f#0@@15| (Tclass._System.___hPartialFunc5 |#$T0@@72| |#$T1@@56| |#$T2@@37| |#$T3@@15| |#$T4@@15| |#$R@@85|)) (and ($Is |f#0@@15| (Tclass._System.___hFunc5 |#$T0@@72| |#$T1@@56| |#$T2@@37| |#$T3@@15| |#$T4@@15| |#$R@@85|)) (forall ((|x0#0@@11| T@U) (|x1#0@@7| T@U) (|x2#0@@3| T@U) (|x3#0| T@U) (|x4#0| T@U) ) (!  (=> (and (and (and (and (and (= (type |x0#0@@11|) BoxType) (= (type |x1#0@@7|) BoxType)) (= (type |x2#0@@3|) BoxType)) (= (type |x3#0|) BoxType)) (= (type |x4#0|) BoxType)) (and (and (and (and ($IsBox |x0#0@@11| |#$T0@@72|) ($IsBox |x1#0@@7| |#$T1@@56|)) ($IsBox |x2#0@@3| |#$T2@@37|)) ($IsBox |x3#0| |#$T3@@15|)) ($IsBox |x4#0| |#$T4@@15|))) (|Set#Equal| (Reads5 |#$T0@@72| |#$T1@@56| |#$T2@@37| |#$T3@@15| |#$T4@@15| |#$R@@85| $OneHeap |f#0@@15| |x0#0@@11| |x1#0@@7| |x2#0@@3| |x3#0| |x4#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |882|
 :no-pattern (type |x0#0@@11|)
 :no-pattern (type |x1#0@@7|)
 :no-pattern (type |x2#0@@3|)
 :no-pattern (type |x3#0|)
 :no-pattern (type |x4#0|)
 :no-pattern (U_2_int |x0#0@@11|)
 :no-pattern (U_2_bool |x0#0@@11|)
 :no-pattern (U_2_int |x1#0@@7|)
 :no-pattern (U_2_bool |x1#0@@7|)
 :no-pattern (U_2_int |x2#0@@3|)
 :no-pattern (U_2_bool |x2#0@@3|)
 :no-pattern (U_2_int |x3#0|)
 :no-pattern (U_2_bool |x3#0|)
 :no-pattern (U_2_int |x4#0|)
 :no-pattern (U_2_bool |x4#0|)
)))) (=> (and ($Is |f#0@@15| (Tclass._System.___hFunc5 |#$T0@@72| |#$T1@@56| |#$T2@@37| |#$T3@@15| |#$T4@@15| |#$R@@85|)) (forall ((|x0#0@@12| T@U) (|x1#0@@8| T@U) (|x2#0@@4| T@U) (|x3#0@@0| T@U) (|x4#0@@0| T@U) ) (!  (=> (and (and (and (and (and (= (type |x0#0@@12|) BoxType) (= (type |x1#0@@8|) BoxType)) (= (type |x2#0@@4|) BoxType)) (= (type |x3#0@@0|) BoxType)) (= (type |x4#0@@0|) BoxType)) (and (and (and (and ($IsBox |x0#0@@12| |#$T0@@72|) ($IsBox |x1#0@@8| |#$T1@@56|)) ($IsBox |x2#0@@4| |#$T2@@37|)) ($IsBox |x3#0@@0| |#$T3@@15|)) ($IsBox |x4#0@@0| |#$T4@@15|))) (|Set#Equal| (Reads5 |#$T0@@72| |#$T1@@56| |#$T2@@37| |#$T3@@15| |#$T4@@15| |#$R@@85| $OneHeap |f#0@@15| |x0#0@@12| |x1#0@@8| |x2#0@@4| |x3#0@@0| |x4#0@@0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |882|
 :no-pattern (type |x0#0@@12|)
 :no-pattern (type |x1#0@@8|)
 :no-pattern (type |x2#0@@4|)
 :no-pattern (type |x3#0@@0|)
 :no-pattern (type |x4#0@@0|)
 :no-pattern (U_2_int |x0#0@@12|)
 :no-pattern (U_2_bool |x0#0@@12|)
 :no-pattern (U_2_int |x1#0@@8|)
 :no-pattern (U_2_bool |x1#0@@8|)
 :no-pattern (U_2_int |x2#0@@4|)
 :no-pattern (U_2_bool |x2#0@@4|)
 :no-pattern (U_2_int |x3#0@@0|)
 :no-pattern (U_2_bool |x3#0@@0|)
 :no-pattern (U_2_int |x4#0@@0|)
 :no-pattern (U_2_bool |x4#0@@0|)
))) ($Is |f#0@@15| (Tclass._System.___hPartialFunc5 |#$T0@@72| |#$T1@@56| |#$T2@@37| |#$T3@@15| |#$T4@@15| |#$R@@85|)))))
 :qid |unknown.0:0|
 :skolemid |883|
 :pattern ( ($Is |f#0@@15| (Tclass._System.___hPartialFunc5 |#$T0@@72| |#$T1@@56| |#$T2@@37| |#$T3@@15| |#$T4@@15| |#$R@@85|)))
)))
(assert (forall ((|#$T0@@73| T@U) (|#$T1@@57| T@U) (|#$T2@@38| T@U) (|#$T3@@16| T@U) (|#$T4@@16| T@U) (|#$R@@86| T@U) (|f#0@@16| T@U) ($h@@16 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type |#$T0@@73|) TyType) (= (type |#$T1@@57|) TyType)) (= (type |#$T2@@38|) TyType)) (= (type |#$T3@@16|) TyType)) (= (type |#$T4@@16|) TyType)) (= (type |#$R@@86|) TyType)) (= (type |f#0@@16|) HandleTypeType)) (= (type $h@@16) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@16| (Tclass._System.___hPartialFunc5 |#$T0@@73| |#$T1@@57| |#$T2@@38| |#$T3@@16| |#$T4@@16| |#$R@@86|) $h@@16) ($IsAlloc |f#0@@16| (Tclass._System.___hFunc5 |#$T0@@73| |#$T1@@57| |#$T2@@38| |#$T3@@16| |#$T4@@16| |#$R@@86|) $h@@16)) (=> ($IsAlloc |f#0@@16| (Tclass._System.___hFunc5 |#$T0@@73| |#$T1@@57| |#$T2@@38| |#$T3@@16| |#$T4@@16| |#$R@@86|) $h@@16) ($IsAlloc |f#0@@16| (Tclass._System.___hPartialFunc5 |#$T0@@73| |#$T1@@57| |#$T2@@38| |#$T3@@16| |#$T4@@16| |#$R@@86|) $h@@16))))
 :qid |unknown.0:0|
 :skolemid |884|
 :pattern ( ($IsAlloc |f#0@@16| (Tclass._System.___hPartialFunc5 |#$T0@@73| |#$T1@@57| |#$T2@@38| |#$T3@@16| |#$T4@@16| |#$R@@86|) $h@@16))
)))
(assert (forall ((arg0@@214 T@U) (arg1@@103 T@U) (arg2@@61 T@U) (arg3@@39 T@U) (arg4@@28 T@U) (arg5@@18 T@U) ) (! (= (type (Tclass._System.___hTotalFunc5 arg0@@214 arg1@@103 arg2@@61 arg3@@39 arg4@@28 arg5@@18)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc5|
 :pattern ( (Tclass._System.___hTotalFunc5 arg0@@214 arg1@@103 arg2@@61 arg3@@39 arg4@@28 arg5@@18))
)))
(assert (forall ((|#$T0@@74| T@U) (|#$T1@@58| T@U) (|#$T2@@39| T@U) (|#$T3@@17| T@U) (|#$T4@@17| T@U) (|#$R@@87| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@74|) TyType) (= (type |#$T1@@58|) TyType)) (= (type |#$T2@@39|) TyType)) (= (type |#$T3@@17|) TyType)) (= (type |#$T4@@17|) TyType)) (= (type |#$R@@87|) TyType)) (= (Tag (Tclass._System.___hTotalFunc5 |#$T0@@74| |#$T1@@58| |#$T2@@39| |#$T3@@17| |#$T4@@17| |#$R@@87|)) Tagclass._System.___hTotalFunc5))
 :qid |unknown.0:0|
 :skolemid |885|
 :pattern ( (Tclass._System.___hTotalFunc5 |#$T0@@74| |#$T1@@58| |#$T2@@39| |#$T3@@17| |#$T4@@17| |#$R@@87|))
)))
(assert (forall ((arg0@@215 T@U) ) (! (= (type (Tclass._System.___hTotalFunc5_0 arg0@@215)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc5_0|
 :pattern ( (Tclass._System.___hTotalFunc5_0 arg0@@215))
)))
(assert (forall ((|#$T0@@75| T@U) (|#$T1@@59| T@U) (|#$T2@@40| T@U) (|#$T3@@18| T@U) (|#$T4@@18| T@U) (|#$R@@88| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@75|) TyType) (= (type |#$T1@@59|) TyType)) (= (type |#$T2@@40|) TyType)) (= (type |#$T3@@18|) TyType)) (= (type |#$T4@@18|) TyType)) (= (type |#$R@@88|) TyType)) (= (Tclass._System.___hTotalFunc5_0 (Tclass._System.___hTotalFunc5 |#$T0@@75| |#$T1@@59| |#$T2@@40| |#$T3@@18| |#$T4@@18| |#$R@@88|)) |#$T0@@75|))
 :qid |unknown.0:0|
 :skolemid |886|
 :pattern ( (Tclass._System.___hTotalFunc5 |#$T0@@75| |#$T1@@59| |#$T2@@40| |#$T3@@18| |#$T4@@18| |#$R@@88|))
)))
(assert (forall ((arg0@@216 T@U) ) (! (= (type (Tclass._System.___hTotalFunc5_1 arg0@@216)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc5_1|
 :pattern ( (Tclass._System.___hTotalFunc5_1 arg0@@216))
)))
(assert (forall ((|#$T0@@76| T@U) (|#$T1@@60| T@U) (|#$T2@@41| T@U) (|#$T3@@19| T@U) (|#$T4@@19| T@U) (|#$R@@89| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@76|) TyType) (= (type |#$T1@@60|) TyType)) (= (type |#$T2@@41|) TyType)) (= (type |#$T3@@19|) TyType)) (= (type |#$T4@@19|) TyType)) (= (type |#$R@@89|) TyType)) (= (Tclass._System.___hTotalFunc5_1 (Tclass._System.___hTotalFunc5 |#$T0@@76| |#$T1@@60| |#$T2@@41| |#$T3@@19| |#$T4@@19| |#$R@@89|)) |#$T1@@60|))
 :qid |unknown.0:0|
 :skolemid |887|
 :pattern ( (Tclass._System.___hTotalFunc5 |#$T0@@76| |#$T1@@60| |#$T2@@41| |#$T3@@19| |#$T4@@19| |#$R@@89|))
)))
(assert (forall ((arg0@@217 T@U) ) (! (= (type (Tclass._System.___hTotalFunc5_2 arg0@@217)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc5_2|
 :pattern ( (Tclass._System.___hTotalFunc5_2 arg0@@217))
)))
(assert (forall ((|#$T0@@77| T@U) (|#$T1@@61| T@U) (|#$T2@@42| T@U) (|#$T3@@20| T@U) (|#$T4@@20| T@U) (|#$R@@90| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@77|) TyType) (= (type |#$T1@@61|) TyType)) (= (type |#$T2@@42|) TyType)) (= (type |#$T3@@20|) TyType)) (= (type |#$T4@@20|) TyType)) (= (type |#$R@@90|) TyType)) (= (Tclass._System.___hTotalFunc5_2 (Tclass._System.___hTotalFunc5 |#$T0@@77| |#$T1@@61| |#$T2@@42| |#$T3@@20| |#$T4@@20| |#$R@@90|)) |#$T2@@42|))
 :qid |unknown.0:0|
 :skolemid |888|
 :pattern ( (Tclass._System.___hTotalFunc5 |#$T0@@77| |#$T1@@61| |#$T2@@42| |#$T3@@20| |#$T4@@20| |#$R@@90|))
)))
(assert (forall ((arg0@@218 T@U) ) (! (= (type (Tclass._System.___hTotalFunc5_3 arg0@@218)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc5_3|
 :pattern ( (Tclass._System.___hTotalFunc5_3 arg0@@218))
)))
(assert (forall ((|#$T0@@78| T@U) (|#$T1@@62| T@U) (|#$T2@@43| T@U) (|#$T3@@21| T@U) (|#$T4@@21| T@U) (|#$R@@91| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@78|) TyType) (= (type |#$T1@@62|) TyType)) (= (type |#$T2@@43|) TyType)) (= (type |#$T3@@21|) TyType)) (= (type |#$T4@@21|) TyType)) (= (type |#$R@@91|) TyType)) (= (Tclass._System.___hTotalFunc5_3 (Tclass._System.___hTotalFunc5 |#$T0@@78| |#$T1@@62| |#$T2@@43| |#$T3@@21| |#$T4@@21| |#$R@@91|)) |#$T3@@21|))
 :qid |unknown.0:0|
 :skolemid |889|
 :pattern ( (Tclass._System.___hTotalFunc5 |#$T0@@78| |#$T1@@62| |#$T2@@43| |#$T3@@21| |#$T4@@21| |#$R@@91|))
)))
(assert (forall ((arg0@@219 T@U) ) (! (= (type (Tclass._System.___hTotalFunc5_4 arg0@@219)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc5_4|
 :pattern ( (Tclass._System.___hTotalFunc5_4 arg0@@219))
)))
(assert (forall ((|#$T0@@79| T@U) (|#$T1@@63| T@U) (|#$T2@@44| T@U) (|#$T3@@22| T@U) (|#$T4@@22| T@U) (|#$R@@92| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@79|) TyType) (= (type |#$T1@@63|) TyType)) (= (type |#$T2@@44|) TyType)) (= (type |#$T3@@22|) TyType)) (= (type |#$T4@@22|) TyType)) (= (type |#$R@@92|) TyType)) (= (Tclass._System.___hTotalFunc5_4 (Tclass._System.___hTotalFunc5 |#$T0@@79| |#$T1@@63| |#$T2@@44| |#$T3@@22| |#$T4@@22| |#$R@@92|)) |#$T4@@22|))
 :qid |unknown.0:0|
 :skolemid |890|
 :pattern ( (Tclass._System.___hTotalFunc5 |#$T0@@79| |#$T1@@63| |#$T2@@44| |#$T3@@22| |#$T4@@22| |#$R@@92|))
)))
(assert (forall ((arg0@@220 T@U) ) (! (= (type (Tclass._System.___hTotalFunc5_5 arg0@@220)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc5_5|
 :pattern ( (Tclass._System.___hTotalFunc5_5 arg0@@220))
)))
(assert (forall ((|#$T0@@80| T@U) (|#$T1@@64| T@U) (|#$T2@@45| T@U) (|#$T3@@23| T@U) (|#$T4@@23| T@U) (|#$R@@93| T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@80|) TyType) (= (type |#$T1@@64|) TyType)) (= (type |#$T2@@45|) TyType)) (= (type |#$T3@@23|) TyType)) (= (type |#$T4@@23|) TyType)) (= (type |#$R@@93|) TyType)) (= (Tclass._System.___hTotalFunc5_5 (Tclass._System.___hTotalFunc5 |#$T0@@80| |#$T1@@64| |#$T2@@45| |#$T3@@23| |#$T4@@23| |#$R@@93|)) |#$R@@93|))
 :qid |unknown.0:0|
 :skolemid |891|
 :pattern ( (Tclass._System.___hTotalFunc5 |#$T0@@80| |#$T1@@64| |#$T2@@45| |#$T3@@23| |#$T4@@23| |#$R@@93|))
)))
(assert (forall ((|#$T0@@81| T@U) (|#$T1@@65| T@U) (|#$T2@@46| T@U) (|#$T3@@24| T@U) (|#$T4@@24| T@U) (|#$R@@94| T@U) (bx@@75 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type |#$T0@@81|) TyType) (= (type |#$T1@@65|) TyType)) (= (type |#$T2@@46|) TyType)) (= (type |#$T3@@24|) TyType)) (= (type |#$T4@@24|) TyType)) (= (type |#$R@@94|) TyType)) (= (type bx@@75) BoxType)) ($IsBox bx@@75 (Tclass._System.___hTotalFunc5 |#$T0@@81| |#$T1@@65| |#$T2@@46| |#$T3@@24| |#$T4@@24| |#$R@@94|))) (and (= ($Box ($Unbox HandleTypeType bx@@75)) bx@@75) ($Is ($Unbox HandleTypeType bx@@75) (Tclass._System.___hTotalFunc5 |#$T0@@81| |#$T1@@65| |#$T2@@46| |#$T3@@24| |#$T4@@24| |#$R@@94|))))
 :qid |unknown.0:0|
 :skolemid |892|
 :pattern ( ($IsBox bx@@75 (Tclass._System.___hTotalFunc5 |#$T0@@81| |#$T1@@65| |#$T2@@46| |#$T3@@24| |#$T4@@24| |#$R@@94|)))
)))
(assert (forall ((|#$T0@@82| T@U) (|#$T1@@66| T@U) (|#$T2@@47| T@U) (|#$T3@@25| T@U) (|#$T4@@25| T@U) (|#$R@@95| T@U) (|f#0@@17| T@U) ) (!  (=> (and (and (and (and (and (and (= (type |#$T0@@82|) TyType) (= (type |#$T1@@66|) TyType)) (= (type |#$T2@@47|) TyType)) (= (type |#$T3@@25|) TyType)) (= (type |#$T4@@25|) TyType)) (= (type |#$R@@95|) TyType)) (= (type |f#0@@17|) HandleTypeType)) (and (=> ($Is |f#0@@17| (Tclass._System.___hTotalFunc5 |#$T0@@82| |#$T1@@66| |#$T2@@47| |#$T3@@25| |#$T4@@25| |#$R@@95|)) (and ($Is |f#0@@17| (Tclass._System.___hPartialFunc5 |#$T0@@82| |#$T1@@66| |#$T2@@47| |#$T3@@25| |#$T4@@25| |#$R@@95|)) (forall ((|x0#0@@13| T@U) (|x1#0@@9| T@U) (|x2#0@@5| T@U) (|x3#0@@1| T@U) (|x4#0@@1| T@U) ) (!  (=> (and (and (and (and (and (= (type |x0#0@@13|) BoxType) (= (type |x1#0@@9|) BoxType)) (= (type |x2#0@@5|) BoxType)) (= (type |x3#0@@1|) BoxType)) (= (type |x4#0@@1|) BoxType)) (and (and (and (and ($IsBox |x0#0@@13| |#$T0@@82|) ($IsBox |x1#0@@9| |#$T1@@66|)) ($IsBox |x2#0@@5| |#$T2@@47|)) ($IsBox |x3#0@@1| |#$T3@@25|)) ($IsBox |x4#0@@1| |#$T4@@25|))) (Requires5 |#$T0@@82| |#$T1@@66| |#$T2@@47| |#$T3@@25| |#$T4@@25| |#$R@@95| $OneHeap |f#0@@17| |x0#0@@13| |x1#0@@9| |x2#0@@5| |x3#0@@1| |x4#0@@1|))
 :qid |unknown.0:0|
 :skolemid |893|
 :no-pattern (type |x0#0@@13|)
 :no-pattern (type |x1#0@@9|)
 :no-pattern (type |x2#0@@5|)
 :no-pattern (type |x3#0@@1|)
 :no-pattern (type |x4#0@@1|)
 :no-pattern (U_2_int |x0#0@@13|)
 :no-pattern (U_2_bool |x0#0@@13|)
 :no-pattern (U_2_int |x1#0@@9|)
 :no-pattern (U_2_bool |x1#0@@9|)
 :no-pattern (U_2_int |x2#0@@5|)
 :no-pattern (U_2_bool |x2#0@@5|)
 :no-pattern (U_2_int |x3#0@@1|)
 :no-pattern (U_2_bool |x3#0@@1|)
 :no-pattern (U_2_int |x4#0@@1|)
 :no-pattern (U_2_bool |x4#0@@1|)
)))) (=> (and ($Is |f#0@@17| (Tclass._System.___hPartialFunc5 |#$T0@@82| |#$T1@@66| |#$T2@@47| |#$T3@@25| |#$T4@@25| |#$R@@95|)) (forall ((|x0#0@@14| T@U) (|x1#0@@10| T@U) (|x2#0@@6| T@U) (|x3#0@@2| T@U) (|x4#0@@2| T@U) ) (!  (=> (and (and (and (and (and (= (type |x0#0@@14|) BoxType) (= (type |x1#0@@10|) BoxType)) (= (type |x2#0@@6|) BoxType)) (= (type |x3#0@@2|) BoxType)) (= (type |x4#0@@2|) BoxType)) (and (and (and (and ($IsBox |x0#0@@14| |#$T0@@82|) ($IsBox |x1#0@@10| |#$T1@@66|)) ($IsBox |x2#0@@6| |#$T2@@47|)) ($IsBox |x3#0@@2| |#$T3@@25|)) ($IsBox |x4#0@@2| |#$T4@@25|))) (Requires5 |#$T0@@82| |#$T1@@66| |#$T2@@47| |#$T3@@25| |#$T4@@25| |#$R@@95| $OneHeap |f#0@@17| |x0#0@@14| |x1#0@@10| |x2#0@@6| |x3#0@@2| |x4#0@@2|))
 :qid |unknown.0:0|
 :skolemid |893|
 :no-pattern (type |x0#0@@14|)
 :no-pattern (type |x1#0@@10|)
 :no-pattern (type |x2#0@@6|)
 :no-pattern (type |x3#0@@2|)
 :no-pattern (type |x4#0@@2|)
 :no-pattern (U_2_int |x0#0@@14|)
 :no-pattern (U_2_bool |x0#0@@14|)
 :no-pattern (U_2_int |x1#0@@10|)
 :no-pattern (U_2_bool |x1#0@@10|)
 :no-pattern (U_2_int |x2#0@@6|)
 :no-pattern (U_2_bool |x2#0@@6|)
 :no-pattern (U_2_int |x3#0@@2|)
 :no-pattern (U_2_bool |x3#0@@2|)
 :no-pattern (U_2_int |x4#0@@2|)
 :no-pattern (U_2_bool |x4#0@@2|)
))) ($Is |f#0@@17| (Tclass._System.___hTotalFunc5 |#$T0@@82| |#$T1@@66| |#$T2@@47| |#$T3@@25| |#$T4@@25| |#$R@@95|)))))
 :qid |unknown.0:0|
 :skolemid |894|
 :pattern ( ($Is |f#0@@17| (Tclass._System.___hTotalFunc5 |#$T0@@82| |#$T1@@66| |#$T2@@47| |#$T3@@25| |#$T4@@25| |#$R@@95|)))
)))
(assert (forall ((|#$T0@@83| T@U) (|#$T1@@67| T@U) (|#$T2@@48| T@U) (|#$T3@@26| T@U) (|#$T4@@26| T@U) (|#$R@@96| T@U) (|f#0@@18| T@U) ($h@@17 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type |#$T0@@83|) TyType) (= (type |#$T1@@67|) TyType)) (= (type |#$T2@@48|) TyType)) (= (type |#$T3@@26|) TyType)) (= (type |#$T4@@26|) TyType)) (= (type |#$R@@96|) TyType)) (= (type |f#0@@18|) HandleTypeType)) (= (type $h@@17) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc |f#0@@18| (Tclass._System.___hTotalFunc5 |#$T0@@83| |#$T1@@67| |#$T2@@48| |#$T3@@26| |#$T4@@26| |#$R@@96|) $h@@17) ($IsAlloc |f#0@@18| (Tclass._System.___hPartialFunc5 |#$T0@@83| |#$T1@@67| |#$T2@@48| |#$T3@@26| |#$T4@@26| |#$R@@96|) $h@@17)) (=> ($IsAlloc |f#0@@18| (Tclass._System.___hPartialFunc5 |#$T0@@83| |#$T1@@67| |#$T2@@48| |#$T3@@26| |#$T4@@26| |#$R@@96|) $h@@17) ($IsAlloc |f#0@@18| (Tclass._System.___hTotalFunc5 |#$T0@@83| |#$T1@@67| |#$T2@@48| |#$T3@@26| |#$T4@@26| |#$R@@96|) $h@@17))))
 :qid |unknown.0:0|
 :skolemid |895|
 :pattern ( ($IsAlloc |f#0@@18| (Tclass._System.___hTotalFunc5 |#$T0@@83| |#$T1@@67| |#$T2@@48| |#$T3@@26| |#$T4@@26| |#$R@@96|) $h@@17))
)))
(assert (forall ((arg0@@221 T@U) (arg1@@104 T@U) ) (! (= (type (|#_System._tuple#2._#Make2| arg0@@221 arg1@@104)) DatatypeTypeType)
 :qid |funType:#_System._tuple#2._#Make2|
 :pattern ( (|#_System._tuple#2._#Make2| arg0@@221 arg1@@104))
)))
(assert (forall ((|a#5#0#0| T@U) (|a#5#1#0| T@U) ) (!  (=> (and (= (type |a#5#0#0|) BoxType) (= (type |a#5#1#0|) BoxType)) (= (DatatypeCtorId (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|)) |##_System._tuple#2._#Make2|))
 :qid |unknown.0:0|
 :skolemid |896|
 :pattern ( (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|))
)))
(assert (forall ((d@@4 T@U) ) (!  (=> (= (type d@@4) DatatypeTypeType) (and (=> (_System.Tuple2.___hMake2_q d@@4) (= (DatatypeCtorId d@@4) |##_System._tuple#2._#Make2|)) (=> (= (DatatypeCtorId d@@4) |##_System._tuple#2._#Make2|) (_System.Tuple2.___hMake2_q d@@4))))
 :qid |unknown.0:0|
 :skolemid |897|
 :pattern ( (_System.Tuple2.___hMake2_q d@@4))
)))
(assert (forall ((d@@5 T@U) ) (!  (=> (and (= (type d@@5) DatatypeTypeType) (_System.Tuple2.___hMake2_q d@@5)) (exists ((|a#6#0#0| T@U) (|a#6#1#0| T@U) ) (!  (and (and (= (type |a#6#0#0|) BoxType) (= (type |a#6#1#0|) BoxType)) (= d@@5 (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|)))
 :qid |unknown.0:0|
 :skolemid |898|
 :no-pattern (type |a#6#0#0|)
 :no-pattern (type |a#6#1#0|)
 :no-pattern (U_2_int |a#6#0#0|)
 :no-pattern (U_2_bool |a#6#0#0|)
 :no-pattern (U_2_int |a#6#1#0|)
 :no-pattern (U_2_bool |a#6#1#0|)
)))
 :qid |unknown.0:0|
 :skolemid |899|
 :pattern ( (_System.Tuple2.___hMake2_q d@@5))
)))
(assert (forall ((arg0@@222 T@U) (arg1@@105 T@U) ) (! (= (type (Tclass._System.Tuple2 arg0@@222 arg1@@105)) TyType)
 :qid |funType:Tclass._System.Tuple2|
 :pattern ( (Tclass._System.Tuple2 arg0@@222 arg1@@105))
)))
(assert (forall ((|#$T0@@84| T@U) (|#$T1@@68| T@U) ) (!  (=> (and (= (type |#$T0@@84|) TyType) (= (type |#$T1@@68|) TyType)) (= (Tag (Tclass._System.Tuple2 |#$T0@@84| |#$T1@@68|)) Tagclass._System.Tuple2))
 :qid |unknown.0:0|
 :skolemid |900|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@84| |#$T1@@68|))
)))
(assert (forall ((arg0@@223 T@U) ) (! (= (type (Tclass._System.Tuple2_0 arg0@@223)) TyType)
 :qid |funType:Tclass._System.Tuple2_0|
 :pattern ( (Tclass._System.Tuple2_0 arg0@@223))
)))
(assert (forall ((|#$T0@@85| T@U) (|#$T1@@69| T@U) ) (!  (=> (and (= (type |#$T0@@85|) TyType) (= (type |#$T1@@69|) TyType)) (= (Tclass._System.Tuple2_0 (Tclass._System.Tuple2 |#$T0@@85| |#$T1@@69|)) |#$T0@@85|))
 :qid |unknown.0:0|
 :skolemid |901|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@85| |#$T1@@69|))
)))
(assert (forall ((arg0@@224 T@U) ) (! (= (type (Tclass._System.Tuple2_1 arg0@@224)) TyType)
 :qid |funType:Tclass._System.Tuple2_1|
 :pattern ( (Tclass._System.Tuple2_1 arg0@@224))
)))
(assert (forall ((|#$T0@@86| T@U) (|#$T1@@70| T@U) ) (!  (=> (and (= (type |#$T0@@86|) TyType) (= (type |#$T1@@70|) TyType)) (= (Tclass._System.Tuple2_1 (Tclass._System.Tuple2 |#$T0@@86| |#$T1@@70|)) |#$T1@@70|))
 :qid |unknown.0:0|
 :skolemid |902|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@86| |#$T1@@70|))
)))
(assert (forall ((|#$T0@@87| T@U) (|#$T1@@71| T@U) (bx@@76 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@87|) TyType) (= (type |#$T1@@71|) TyType)) (= (type bx@@76) BoxType)) ($IsBox bx@@76 (Tclass._System.Tuple2 |#$T0@@87| |#$T1@@71|))) (and (= ($Box ($Unbox DatatypeTypeType bx@@76)) bx@@76) ($Is ($Unbox DatatypeTypeType bx@@76) (Tclass._System.Tuple2 |#$T0@@87| |#$T1@@71|))))
 :qid |unknown.0:0|
 :skolemid |903|
 :pattern ( ($IsBox bx@@76 (Tclass._System.Tuple2 |#$T0@@87| |#$T1@@71|)))
)))
(assert (forall ((|#$T0@@88| T@U) (|#$T1@@72| T@U) (|a#7#0#0| T@U) (|a#7#1#0| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@88|) TyType) (= (type |#$T1@@72|) TyType)) (= (type |a#7#0#0|) BoxType)) (= (type |a#7#1#0|) BoxType)) (and (=> ($Is (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|) (Tclass._System.Tuple2 |#$T0@@88| |#$T1@@72|)) (and ($IsBox |a#7#0#0| |#$T0@@88|) ($IsBox |a#7#1#0| |#$T1@@72|))) (=> (and ($IsBox |a#7#0#0| |#$T0@@88|) ($IsBox |a#7#1#0| |#$T1@@72|)) ($Is (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|) (Tclass._System.Tuple2 |#$T0@@88| |#$T1@@72|)))))
 :qid |unknown.0:0|
 :skolemid |904|
 :pattern ( ($Is (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|) (Tclass._System.Tuple2 |#$T0@@88| |#$T1@@72|)))
)))
(assert (forall ((|#$T0@@89| T@U) (|#$T1@@73| T@U) (|a#8#0#0| T@U) (|a#8#1#0| T@U) ($h@@18 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@89|) TyType) (= (type |#$T1@@73|) TyType)) (= (type |a#8#0#0|) BoxType)) (= (type |a#8#1#0|) BoxType)) (= (type $h@@18) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@18)) (and (=> ($IsAlloc (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|) (Tclass._System.Tuple2 |#$T0@@89| |#$T1@@73|) $h@@18) (and ($IsAllocBox |a#8#0#0| |#$T0@@89| $h@@18) ($IsAllocBox |a#8#1#0| |#$T1@@73| $h@@18))) (=> (and ($IsAllocBox |a#8#0#0| |#$T0@@89| $h@@18) ($IsAllocBox |a#8#1#0| |#$T1@@73| $h@@18)) ($IsAlloc (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|) (Tclass._System.Tuple2 |#$T0@@89| |#$T1@@73|) $h@@18))))
 :qid |unknown.0:0|
 :skolemid |905|
 :pattern ( ($IsAlloc (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|) (Tclass._System.Tuple2 |#$T0@@89| |#$T1@@73|) $h@@18))
)))
(assert (forall ((d@@6 T@U) (|#$T0@@90| T@U) ($h@@19 T@U) ) (!  (=> (and (and (and (= (type d@@6) DatatypeTypeType) (= (type |#$T0@@90|) TyType)) (= (type $h@@19) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@19) (and (_System.Tuple2.___hMake2_q d@@6) (exists ((|#$T1@@74| T@U) ) (!  (and (= (type |#$T1@@74|) TyType) ($IsAlloc d@@6 (Tclass._System.Tuple2 |#$T0@@90| |#$T1@@74|) $h@@19))
 :qid |unknown.0:0|
 :skolemid |906|
 :pattern ( ($IsAlloc d@@6 (Tclass._System.Tuple2 |#$T0@@90| |#$T1@@74|) $h@@19))
))))) ($IsAllocBox (_System.Tuple2._0 d@@6) |#$T0@@90| $h@@19))
 :qid |unknown.0:0|
 :skolemid |907|
 :pattern ( ($IsAllocBox (_System.Tuple2._0 d@@6) |#$T0@@90| $h@@19))
)))
(assert (forall ((d@@7 T@U) (|#$T1@@75| T@U) ($h@@20 T@U) ) (!  (=> (and (and (and (= (type d@@7) DatatypeTypeType) (= (type |#$T1@@75|) TyType)) (= (type $h@@20) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@20) (and (_System.Tuple2.___hMake2_q d@@7) (exists ((|#$T0@@91| T@U) ) (!  (and (= (type |#$T0@@91|) TyType) ($IsAlloc d@@7 (Tclass._System.Tuple2 |#$T0@@91| |#$T1@@75|) $h@@20))
 :qid |unknown.0:0|
 :skolemid |908|
 :pattern ( ($IsAlloc d@@7 (Tclass._System.Tuple2 |#$T0@@91| |#$T1@@75|) $h@@20))
))))) ($IsAllocBox (_System.Tuple2._1 d@@7) |#$T1@@75| $h@@20))
 :qid |unknown.0:0|
 :skolemid |909|
 :pattern ( ($IsAllocBox (_System.Tuple2._1 d@@7) |#$T1@@75| $h@@20))
)))
(assert (forall ((|a#9#0#0| T@U) (|a#9#1#0| T@U) ) (!  (=> (and (= (type |a#9#0#0|) BoxType) (= (type |a#9#1#0|) BoxType)) (= (|#_System._tuple#2._#Make2| (Lit |a#9#0#0|) (Lit |a#9#1#0|)) (Lit (|#_System._tuple#2._#Make2| |a#9#0#0| |a#9#1#0|))))
 :qid |unknown.0:0|
 :skolemid |910|
 :pattern ( (|#_System._tuple#2._#Make2| (Lit |a#9#0#0|) (Lit |a#9#1#0|)))
)))
(assert (forall ((|a#10#0#0| T@U) (|a#10#1#0| T@U) ) (!  (=> (and (= (type |a#10#0#0|) BoxType) (= (type |a#10#1#0|) BoxType)) (= (_System.Tuple2._0 (|#_System._tuple#2._#Make2| |a#10#0#0| |a#10#1#0|)) |a#10#0#0|))
 :qid |unknown.0:0|
 :skolemid |911|
 :pattern ( (|#_System._tuple#2._#Make2| |a#10#0#0| |a#10#1#0|))
)))
(assert (forall ((|a#11#0#0| T@U) (|a#11#1#0| T@U) ) (!  (=> (and (= (type |a#11#0#0|) BoxType) (= (type |a#11#1#0|) BoxType)) (< (BoxRank |a#11#0#0|) (DtRank (|#_System._tuple#2._#Make2| |a#11#0#0| |a#11#1#0|))))
 :qid |unknown.0:0|
 :skolemid |912|
 :pattern ( (|#_System._tuple#2._#Make2| |a#11#0#0| |a#11#1#0|))
)))
(assert (forall ((|a#12#0#0| T@U) (|a#12#1#0| T@U) ) (!  (=> (and (= (type |a#12#0#0|) BoxType) (= (type |a#12#1#0|) BoxType)) (= (_System.Tuple2._1 (|#_System._tuple#2._#Make2| |a#12#0#0| |a#12#1#0|)) |a#12#1#0|))
 :qid |unknown.0:0|
 :skolemid |913|
 :pattern ( (|#_System._tuple#2._#Make2| |a#12#0#0| |a#12#1#0|))
)))
(assert (forall ((|a#13#0#0| T@U) (|a#13#1#0| T@U) ) (!  (=> (and (= (type |a#13#0#0|) BoxType) (= (type |a#13#1#0|) BoxType)) (< (BoxRank |a#13#1#0|) (DtRank (|#_System._tuple#2._#Make2| |a#13#0#0| |a#13#1#0|))))
 :qid |unknown.0:0|
 :skolemid |914|
 :pattern ( (|#_System._tuple#2._#Make2| |a#13#0#0| |a#13#1#0|))
)))
(assert (forall ((d@@8 T@U) ) (!  (=> (and (= (type d@@8) DatatypeTypeType) (|$IsA#_System.Tuple2| d@@8)) (_System.Tuple2.___hMake2_q d@@8))
 :qid |unknown.0:0|
 :skolemid |915|
 :pattern ( (|$IsA#_System.Tuple2| d@@8))
)))
(assert (forall ((|#$T0@@92| T@U) (|#$T1@@76| T@U) (d@@9 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@92|) TyType) (= (type |#$T1@@76|) TyType)) (= (type d@@9) DatatypeTypeType)) ($Is d@@9 (Tclass._System.Tuple2 |#$T0@@92| |#$T1@@76|))) (_System.Tuple2.___hMake2_q d@@9))
 :qid |unknown.0:0|
 :skolemid |916|
 :pattern ( (_System.Tuple2.___hMake2_q d@@9) ($Is d@@9 (Tclass._System.Tuple2 |#$T0@@92| |#$T1@@76|)))
)))
(assert (forall ((a@@111 T@U) (b@@60 T@U) ) (!  (=> (and (and (= (type a@@111) DatatypeTypeType) (= (type b@@60) DatatypeTypeType)) true) (and (=> (|_System.Tuple2#Equal| a@@111 b@@60) (and (= (_System.Tuple2._0 a@@111) (_System.Tuple2._0 b@@60)) (= (_System.Tuple2._1 a@@111) (_System.Tuple2._1 b@@60)))) (=> (and (= (_System.Tuple2._0 a@@111) (_System.Tuple2._0 b@@60)) (= (_System.Tuple2._1 a@@111) (_System.Tuple2._1 b@@60))) (|_System.Tuple2#Equal| a@@111 b@@60))))
 :qid |unknown.0:0|
 :skolemid |917|
 :pattern ( (|_System.Tuple2#Equal| a@@111 b@@60))
)))
(assert (forall ((a@@112 T@U) (b@@61 T@U) ) (!  (=> (and (= (type a@@112) DatatypeTypeType) (= (type b@@61) DatatypeTypeType)) (and (=> (|_System.Tuple2#Equal| a@@112 b@@61) (= a@@112 b@@61)) (=> (= a@@112 b@@61) (|_System.Tuple2#Equal| a@@112 b@@61))))
 :qid |unknown.0:0|
 :skolemid |918|
 :pattern ( (|_System.Tuple2#Equal| a@@112 b@@61))
)))
(assert (= (type |#_module.Option.None|) DatatypeTypeType))
(assert (= (DatatypeCtorId |#_module.Option.None|) |##_module.Option.None|))
(assert (forall ((d@@10 T@U) ) (!  (=> (= (type d@@10) DatatypeTypeType) (and (=> (_module.Option.None_q d@@10) (= (DatatypeCtorId d@@10) |##_module.Option.None|)) (=> (= (DatatypeCtorId d@@10) |##_module.Option.None|) (_module.Option.None_q d@@10))))
 :qid |unknown.0:0|
 :skolemid |919|
 :pattern ( (_module.Option.None_q d@@10))
)))
(assert (forall ((d@@11 T@U) ) (!  (=> (and (= (type d@@11) DatatypeTypeType) (_module.Option.None_q d@@11)) (= d@@11 |#_module.Option.None|))
 :qid |unknown.0:0|
 :skolemid |920|
 :pattern ( (_module.Option.None_q d@@11))
)))
(assert (forall ((arg0@@225 T@U) ) (! (= (type (Tclass._module.Option arg0@@225)) TyType)
 :qid |funType:Tclass._module.Option|
 :pattern ( (Tclass._module.Option arg0@@225))
)))
(assert (forall ((_module.Option$V T@U) ) (!  (=> (= (type _module.Option$V) TyType) (= (Tag (Tclass._module.Option _module.Option$V)) Tagclass._module.Option))
 :qid |unknown.0:0|
 :skolemid |921|
 :pattern ( (Tclass._module.Option _module.Option$V))
)))
(assert (forall ((arg0@@226 T@U) ) (! (= (type (Tclass._module.Option_0 arg0@@226)) TyType)
 :qid |funType:Tclass._module.Option_0|
 :pattern ( (Tclass._module.Option_0 arg0@@226))
)))
(assert (forall ((_module.Option$V@@0 T@U) ) (!  (=> (= (type _module.Option$V@@0) TyType) (= (Tclass._module.Option_0 (Tclass._module.Option _module.Option$V@@0)) _module.Option$V@@0))
 :qid |unknown.0:0|
 :skolemid |922|
 :pattern ( (Tclass._module.Option _module.Option$V@@0))
)))
(assert (forall ((_module.Option$V@@1 T@U) (bx@@77 T@U) ) (!  (=> (and (and (= (type _module.Option$V@@1) TyType) (= (type bx@@77) BoxType)) ($IsBox bx@@77 (Tclass._module.Option _module.Option$V@@1))) (and (= ($Box ($Unbox DatatypeTypeType bx@@77)) bx@@77) ($Is ($Unbox DatatypeTypeType bx@@77) (Tclass._module.Option _module.Option$V@@1))))
 :qid |unknown.0:0|
 :skolemid |923|
 :pattern ( ($IsBox bx@@77 (Tclass._module.Option _module.Option$V@@1)))
)))
(assert (forall ((_module.Option$V@@2 T@U) ) (!  (=> (= (type _module.Option$V@@2) TyType) ($Is |#_module.Option.None| (Tclass._module.Option _module.Option$V@@2)))
 :qid |unknown.0:0|
 :skolemid |924|
 :pattern ( ($Is |#_module.Option.None| (Tclass._module.Option _module.Option$V@@2)))
)))
(assert (forall ((_module.Option$V@@3 T@U) ($h@@21 T@U) ) (!  (=> (and (and (= (type _module.Option$V@@3) TyType) (= (type $h@@21) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@21)) ($IsAlloc |#_module.Option.None| (Tclass._module.Option _module.Option$V@@3) $h@@21))
 :qid |unknown.0:0|
 :skolemid |925|
 :pattern ( ($IsAlloc |#_module.Option.None| (Tclass._module.Option _module.Option$V@@3) $h@@21))
)))
(assert (= |#_module.Option.None| (Lit |#_module.Option.None|)))
(assert (forall ((arg0@@227 T@U) ) (! (= (type (|#_module.Option.Some| arg0@@227)) DatatypeTypeType)
 :qid |funType:#_module.Option.Some|
 :pattern ( (|#_module.Option.Some| arg0@@227))
)))
(assert (forall ((|a#19#0#0| T@U) ) (!  (=> (= (type |a#19#0#0|) BoxType) (= (DatatypeCtorId (|#_module.Option.Some| |a#19#0#0|)) |##_module.Option.Some|))
 :qid |DLLDafny.32:34|
 :skolemid |926|
 :pattern ( (|#_module.Option.Some| |a#19#0#0|))
)))
(assert (forall ((d@@12 T@U) ) (!  (=> (= (type d@@12) DatatypeTypeType) (and (=> (_module.Option.Some_q d@@12) (= (DatatypeCtorId d@@12) |##_module.Option.Some|)) (=> (= (DatatypeCtorId d@@12) |##_module.Option.Some|) (_module.Option.Some_q d@@12))))
 :qid |unknown.0:0|
 :skolemid |927|
 :pattern ( (_module.Option.Some_q d@@12))
)))
(assert (forall ((d@@13 T@U) ) (!  (=> (and (= (type d@@13) DatatypeTypeType) (_module.Option.Some_q d@@13)) (exists ((|a#20#0#0| T@U) ) (!  (and (= (type |a#20#0#0|) BoxType) (= d@@13 (|#_module.Option.Some| |a#20#0#0|)))
 :qid |DLLDafny.32:34|
 :skolemid |928|
 :no-pattern (type |a#20#0#0|)
 :no-pattern (U_2_int |a#20#0#0|)
 :no-pattern (U_2_bool |a#20#0#0|)
)))
 :qid |unknown.0:0|
 :skolemid |929|
 :pattern ( (_module.Option.Some_q d@@13))
)))
(assert (forall ((_module.Option$V@@4 T@U) (|a#21#0#0| T@U) ) (!  (=> (and (= (type _module.Option$V@@4) TyType) (= (type |a#21#0#0|) BoxType)) (and (=> ($Is (|#_module.Option.Some| |a#21#0#0|) (Tclass._module.Option _module.Option$V@@4)) ($IsBox |a#21#0#0| _module.Option$V@@4)) (=> ($IsBox |a#21#0#0| _module.Option$V@@4) ($Is (|#_module.Option.Some| |a#21#0#0|) (Tclass._module.Option _module.Option$V@@4)))))
 :qid |unknown.0:0|
 :skolemid |930|
 :pattern ( ($Is (|#_module.Option.Some| |a#21#0#0|) (Tclass._module.Option _module.Option$V@@4)))
)))
(assert (forall ((_module.Option$V@@5 T@U) (|a#22#0#0| T@U) ($h@@22 T@U) ) (!  (=> (and (and (and (= (type _module.Option$V@@5) TyType) (= (type |a#22#0#0|) BoxType)) (= (type $h@@22) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@22)) (and (=> ($IsAlloc (|#_module.Option.Some| |a#22#0#0|) (Tclass._module.Option _module.Option$V@@5) $h@@22) ($IsAllocBox |a#22#0#0| _module.Option$V@@5 $h@@22)) (=> ($IsAllocBox |a#22#0#0| _module.Option$V@@5 $h@@22) ($IsAlloc (|#_module.Option.Some| |a#22#0#0|) (Tclass._module.Option _module.Option$V@@5) $h@@22))))
 :qid |unknown.0:0|
 :skolemid |931|
 :pattern ( ($IsAlloc (|#_module.Option.Some| |a#22#0#0|) (Tclass._module.Option _module.Option$V@@5) $h@@22))
)))
(assert (forall ((arg0@@228 T@U) ) (! (= (type (_module.Option.value arg0@@228)) BoxType)
 :qid |funType:_module.Option.value|
 :pattern ( (_module.Option.value arg0@@228))
)))
(assert (forall ((d@@14 T@U) (_module.Option$V@@6 T@U) ($h@@23 T@U) ) (!  (=> (and (and (and (= (type d@@14) DatatypeTypeType) (= (type _module.Option$V@@6) TyType)) (= (type $h@@23) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@23) (and (_module.Option.Some_q d@@14) ($IsAlloc d@@14 (Tclass._module.Option _module.Option$V@@6) $h@@23)))) ($IsAllocBox (_module.Option.value d@@14) _module.Option$V@@6 $h@@23))
 :qid |unknown.0:0|
 :skolemid |932|
 :pattern ( ($IsAllocBox (_module.Option.value d@@14) _module.Option$V@@6 $h@@23))
)))
(assert (forall ((|a#23#0#0| T@U) ) (!  (=> (= (type |a#23#0#0|) BoxType) (= (|#_module.Option.Some| (Lit |a#23#0#0|)) (Lit (|#_module.Option.Some| |a#23#0#0|))))
 :qid |DLLDafny.32:34|
 :skolemid |933|
 :pattern ( (|#_module.Option.Some| (Lit |a#23#0#0|)))
)))
(assert (forall ((|a#24#0#0| T@U) ) (!  (=> (= (type |a#24#0#0|) BoxType) (= (_module.Option.value (|#_module.Option.Some| |a#24#0#0|)) |a#24#0#0|))
 :qid |DLLDafny.32:34|
 :skolemid |934|
 :pattern ( (|#_module.Option.Some| |a#24#0#0|))
)))
(assert (forall ((|a#25#0#0| T@U) ) (!  (=> (= (type |a#25#0#0|) BoxType) (< (BoxRank |a#25#0#0|) (DtRank (|#_module.Option.Some| |a#25#0#0|))))
 :qid |DLLDafny.32:34|
 :skolemid |935|
 :pattern ( (|#_module.Option.Some| |a#25#0#0|))
)))
(assert (forall ((d@@15 T@U) ) (!  (=> (and (= (type d@@15) DatatypeTypeType) (|$IsA#_module.Option| d@@15)) (or (_module.Option.None_q d@@15) (_module.Option.Some_q d@@15)))
 :qid |unknown.0:0|
 :skolemid |936|
 :pattern ( (|$IsA#_module.Option| d@@15))
)))
(assert (forall ((_module.Option$V@@7 T@U) (d@@16 T@U) ) (!  (=> (and (and (= (type _module.Option$V@@7) TyType) (= (type d@@16) DatatypeTypeType)) ($Is d@@16 (Tclass._module.Option _module.Option$V@@7))) (or (_module.Option.None_q d@@16) (_module.Option.Some_q d@@16)))
 :qid |unknown.0:0|
 :skolemid |937|
 :pattern ( (_module.Option.Some_q d@@16) ($Is d@@16 (Tclass._module.Option _module.Option$V@@7)))
 :pattern ( (_module.Option.None_q d@@16) ($Is d@@16 (Tclass._module.Option _module.Option$V@@7)))
)))
(assert (forall ((a@@113 T@U) (b@@62 T@U) ) (!  (=> (and (and (= (type a@@113) DatatypeTypeType) (= (type b@@62) DatatypeTypeType)) (and (_module.Option.None_q a@@113) (_module.Option.None_q b@@62))) (and (=> (|_module.Option#Equal| a@@113 b@@62) true) (=> true (|_module.Option#Equal| a@@113 b@@62))))
 :qid |unknown.0:0|
 :skolemid |938|
 :pattern ( (|_module.Option#Equal| a@@113 b@@62) (_module.Option.None_q a@@113))
 :pattern ( (|_module.Option#Equal| a@@113 b@@62) (_module.Option.None_q b@@62))
)))
(assert (forall ((a@@114 T@U) (b@@63 T@U) ) (!  (=> (and (and (= (type a@@114) DatatypeTypeType) (= (type b@@63) DatatypeTypeType)) (and (_module.Option.Some_q a@@114) (_module.Option.Some_q b@@63))) (and (=> (|_module.Option#Equal| a@@114 b@@63) (= (_module.Option.value a@@114) (_module.Option.value b@@63))) (=> (= (_module.Option.value a@@114) (_module.Option.value b@@63)) (|_module.Option#Equal| a@@114 b@@63))))
 :qid |unknown.0:0|
 :skolemid |939|
 :pattern ( (|_module.Option#Equal| a@@114 b@@63) (_module.Option.Some_q a@@114))
 :pattern ( (|_module.Option#Equal| a@@114 b@@63) (_module.Option.Some_q b@@63))
)))
(assert (forall ((a@@115 T@U) (b@@64 T@U) ) (!  (=> (and (= (type a@@115) DatatypeTypeType) (= (type b@@64) DatatypeTypeType)) (and (=> (|_module.Option#Equal| a@@115 b@@64) (= a@@115 b@@64)) (=> (= a@@115 b@@64) (|_module.Option#Equal| a@@115 b@@64))))
 :qid |unknown.0:0|
 :skolemid |940|
 :pattern ( (|_module.Option#Equal| a@@115 b@@64))
)))
(assert (forall ((arg0@@229 T@U) (arg1@@106 Int) (arg2@@62 Int) ) (! (= (type (|#_module.Node.Node| arg0@@229 arg1@@106 arg2@@62)) DatatypeTypeType)
 :qid |funType:#_module.Node.Node|
 :pattern ( (|#_module.Node.Node| arg0@@229 arg1@@106 arg2@@62))
)))
(assert (forall ((|a#26#0#0| T@U) (|a#26#1#0| Int) (|a#26#2#0| Int) ) (!  (=> (= (type |a#26#0#0|) DatatypeTypeType) (= (DatatypeCtorId (|#_module.Node.Node| |a#26#0#0| |a#26#1#0| |a#26#2#0|)) |##_module.Node.Node|))
 :qid |DLLDafny.75:25|
 :skolemid |941|
 :pattern ( (|#_module.Node.Node| |a#26#0#0| |a#26#1#0| |a#26#2#0|))
)))
(assert (forall ((d@@17 T@U) ) (!  (=> (= (type d@@17) DatatypeTypeType) (and (=> (_module.Node.Node_q d@@17) (= (DatatypeCtorId d@@17) |##_module.Node.Node|)) (=> (= (DatatypeCtorId d@@17) |##_module.Node.Node|) (_module.Node.Node_q d@@17))))
 :qid |unknown.0:0|
 :skolemid |942|
 :pattern ( (_module.Node.Node_q d@@17))
)))
(assert (forall ((d@@18 T@U) ) (!  (=> (and (= (type d@@18) DatatypeTypeType) (_module.Node.Node_q d@@18)) (exists ((|a#27#0#0| T@U) (|a#27#1#0| Int) (|a#27#2#0| Int) ) (!  (and (= (type |a#27#0#0|) DatatypeTypeType) (= d@@18 (|#_module.Node.Node| |a#27#0#0| |a#27#1#0| |a#27#2#0|)))
 :qid |DLLDafny.75:25|
 :skolemid |943|
 :no-pattern (type |a#27#0#0|)
 :no-pattern (U_2_int |a#27#0#0|)
 :no-pattern (U_2_bool |a#27#0#0|)
)))
 :qid |unknown.0:0|
 :skolemid |944|
 :pattern ( (_module.Node.Node_q d@@18))
)))
(assert (forall ((arg0@@230 T@U) ) (! (= (type (Tclass._module.Node arg0@@230)) TyType)
 :qid |funType:Tclass._module.Node|
 :pattern ( (Tclass._module.Node arg0@@230))
)))
(assert (forall ((_module.Node$A T@U) ) (!  (=> (= (type _module.Node$A) TyType) (= (Tag (Tclass._module.Node _module.Node$A)) Tagclass._module.Node))
 :qid |unknown.0:0|
 :skolemid |945|
 :pattern ( (Tclass._module.Node _module.Node$A))
)))
(assert (forall ((arg0@@231 T@U) ) (! (= (type (Tclass._module.Node_0 arg0@@231)) TyType)
 :qid |funType:Tclass._module.Node_0|
 :pattern ( (Tclass._module.Node_0 arg0@@231))
)))
(assert (forall ((_module.Node$A@@0 T@U) ) (!  (=> (= (type _module.Node$A@@0) TyType) (= (Tclass._module.Node_0 (Tclass._module.Node _module.Node$A@@0)) _module.Node$A@@0))
 :qid |unknown.0:0|
 :skolemid |946|
 :pattern ( (Tclass._module.Node _module.Node$A@@0))
)))
(assert (forall ((_module.Node$A@@1 T@U) (bx@@78 T@U) ) (!  (=> (and (and (= (type _module.Node$A@@1) TyType) (= (type bx@@78) BoxType)) ($IsBox bx@@78 (Tclass._module.Node _module.Node$A@@1))) (and (= ($Box ($Unbox DatatypeTypeType bx@@78)) bx@@78) ($Is ($Unbox DatatypeTypeType bx@@78) (Tclass._module.Node _module.Node$A@@1))))
 :qid |unknown.0:0|
 :skolemid |947|
 :pattern ( ($IsBox bx@@78 (Tclass._module.Node _module.Node$A@@1)))
)))
(assert (forall ((_module.Node$A@@2 T@U) (|a#28#0#0| T@U) (|a#28#1#0| Int) (|a#28#2#0| Int) ) (!  (=> (and (= (type _module.Node$A@@2) TyType) (= (type |a#28#0#0|) DatatypeTypeType)) (and (=> ($Is (|#_module.Node.Node| |a#28#0#0| |a#28#1#0| |a#28#2#0|) (Tclass._module.Node _module.Node$A@@2)) (and (and ($Is |a#28#0#0| (Tclass._module.Option _module.Node$A@@2)) ($Is (int_2_U |a#28#1#0|) TInt)) ($Is (int_2_U |a#28#2#0|) TInt))) (=> (and (and ($Is |a#28#0#0| (Tclass._module.Option _module.Node$A@@2)) ($Is (int_2_U |a#28#1#0|) TInt)) ($Is (int_2_U |a#28#2#0|) TInt)) ($Is (|#_module.Node.Node| |a#28#0#0| |a#28#1#0| |a#28#2#0|) (Tclass._module.Node _module.Node$A@@2)))))
 :qid |unknown.0:0|
 :skolemid |948|
 :pattern ( ($Is (|#_module.Node.Node| |a#28#0#0| |a#28#1#0| |a#28#2#0|) (Tclass._module.Node _module.Node$A@@2)))
)))
(assert (forall ((_module.Node$A@@3 T@U) (|a#29#0#0| T@U) (|a#29#1#0| Int) (|a#29#2#0| Int) ($h@@24 T@U) ) (!  (=> (and (and (and (= (type _module.Node$A@@3) TyType) (= (type |a#29#0#0|) DatatypeTypeType)) (= (type $h@@24) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@24)) (and (=> ($IsAlloc (|#_module.Node.Node| |a#29#0#0| |a#29#1#0| |a#29#2#0|) (Tclass._module.Node _module.Node$A@@3) $h@@24) (and (and ($IsAlloc |a#29#0#0| (Tclass._module.Option _module.Node$A@@3) $h@@24) ($IsAlloc (int_2_U |a#29#1#0|) TInt $h@@24)) ($IsAlloc (int_2_U |a#29#2#0|) TInt $h@@24))) (=> (and (and ($IsAlloc |a#29#0#0| (Tclass._module.Option _module.Node$A@@3) $h@@24) ($IsAlloc (int_2_U |a#29#1#0|) TInt $h@@24)) ($IsAlloc (int_2_U |a#29#2#0|) TInt $h@@24)) ($IsAlloc (|#_module.Node.Node| |a#29#0#0| |a#29#1#0| |a#29#2#0|) (Tclass._module.Node _module.Node$A@@3) $h@@24))))
 :qid |unknown.0:0|
 :skolemid |949|
 :pattern ( ($IsAlloc (|#_module.Node.Node| |a#29#0#0| |a#29#1#0| |a#29#2#0|) (Tclass._module.Node _module.Node$A@@3) $h@@24))
)))
(assert (forall ((arg0@@232 T@U) ) (! (= (type (_module.Node.data arg0@@232)) DatatypeTypeType)
 :qid |funType:_module.Node.data|
 :pattern ( (_module.Node.data arg0@@232))
)))
(assert (forall ((d@@19 T@U) (_module.Node$A@@4 T@U) ($h@@25 T@U) ) (!  (=> (and (and (and (= (type d@@19) DatatypeTypeType) (= (type _module.Node$A@@4) TyType)) (= (type $h@@25) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@25) (and (_module.Node.Node_q d@@19) ($IsAlloc d@@19 (Tclass._module.Node _module.Node$A@@4) $h@@25)))) ($IsAlloc (_module.Node.data d@@19) (Tclass._module.Option _module.Node$A@@4) $h@@25))
 :qid |unknown.0:0|
 :skolemid |950|
 :pattern ( ($IsAlloc (_module.Node.data d@@19) (Tclass._module.Option _module.Node$A@@4) $h@@25))
)))
(assert (forall ((d@@20 T@U) ($h@@26 T@U) ) (!  (=> (and (and (= (type d@@20) DatatypeTypeType) (= (type $h@@26) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@26) (and (_module.Node.Node_q d@@20) (exists ((_module.Node$A@@5 T@U) ) (!  (and (= (type _module.Node$A@@5) TyType) ($IsAlloc d@@20 (Tclass._module.Node _module.Node$A@@5) $h@@26))
 :qid |unknown.0:0|
 :skolemid |951|
 :pattern ( ($IsAlloc d@@20 (Tclass._module.Node _module.Node$A@@5) $h@@26))
))))) ($IsAlloc (int_2_U (_module.Node.next d@@20)) TInt $h@@26))
 :qid |unknown.0:0|
 :skolemid |952|
 :pattern ( ($IsAlloc (int_2_U (_module.Node.next d@@20)) TInt $h@@26))
)))
(assert (forall ((d@@21 T@U) ($h@@27 T@U) ) (!  (=> (and (and (= (type d@@21) DatatypeTypeType) (= (type $h@@27) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@27) (and (_module.Node.Node_q d@@21) (exists ((_module.Node$A@@6 T@U) ) (!  (and (= (type _module.Node$A@@6) TyType) ($IsAlloc d@@21 (Tclass._module.Node _module.Node$A@@6) $h@@27))
 :qid |unknown.0:0|
 :skolemid |953|
 :pattern ( ($IsAlloc d@@21 (Tclass._module.Node _module.Node$A@@6) $h@@27))
))))) ($IsAlloc (int_2_U (_module.Node.prev d@@21)) TInt $h@@27))
 :qid |unknown.0:0|
 :skolemid |954|
 :pattern ( ($IsAlloc (int_2_U (_module.Node.prev d@@21)) TInt $h@@27))
)))
(assert (forall ((|a#30#0#0| T@U) (|a#30#1#0| Int) (|a#30#2#0| Int) ) (!  (=> (= (type |a#30#0#0|) DatatypeTypeType) (= (|#_module.Node.Node| (Lit |a#30#0#0|) |a#30#1#0| |a#30#2#0|) (Lit (|#_module.Node.Node| |a#30#0#0| |a#30#1#0| |a#30#2#0|))))
 :qid |DLLDafny.75:25|
 :skolemid |955|
 :pattern ( (|#_module.Node.Node| (Lit |a#30#0#0|) |a#30#1#0| |a#30#2#0|))
)))
(assert (forall ((|a#31#0#0| T@U) (|a#31#1#0| Int) (|a#31#2#0| Int) ) (!  (=> (= (type |a#31#0#0|) DatatypeTypeType) (= (_module.Node.data (|#_module.Node.Node| |a#31#0#0| |a#31#1#0| |a#31#2#0|)) |a#31#0#0|))
 :qid |DLLDafny.75:25|
 :skolemid |956|
 :pattern ( (|#_module.Node.Node| |a#31#0#0| |a#31#1#0| |a#31#2#0|))
)))
(assert (forall ((|a#32#0#0| T@U) (|a#32#1#0| Int) (|a#32#2#0| Int) ) (!  (=> (= (type |a#32#0#0|) DatatypeTypeType) (< (DtRank |a#32#0#0|) (DtRank (|#_module.Node.Node| |a#32#0#0| |a#32#1#0| |a#32#2#0|))))
 :qid |DLLDafny.75:25|
 :skolemid |957|
 :pattern ( (|#_module.Node.Node| |a#32#0#0| |a#32#1#0| |a#32#2#0|))
)))
(assert (forall ((|a#33#0#0| T@U) (|a#33#1#0| Int) (|a#33#2#0| Int) ) (!  (=> (= (type |a#33#0#0|) DatatypeTypeType) (= (_module.Node.next (|#_module.Node.Node| |a#33#0#0| |a#33#1#0| |a#33#2#0|)) |a#33#1#0|))
 :qid |DLLDafny.75:25|
 :skolemid |958|
 :pattern ( (|#_module.Node.Node| |a#33#0#0| |a#33#1#0| |a#33#2#0|))
)))
(assert (forall ((|a#34#0#0| T@U) (|a#34#1#0| Int) (|a#34#2#0| Int) ) (!  (=> (= (type |a#34#0#0|) DatatypeTypeType) (= (_module.Node.prev (|#_module.Node.Node| |a#34#0#0| |a#34#1#0| |a#34#2#0|)) |a#34#2#0|))
 :qid |DLLDafny.75:25|
 :skolemid |959|
 :pattern ( (|#_module.Node.Node| |a#34#0#0| |a#34#1#0| |a#34#2#0|))
)))
(assert (forall ((d@@22 T@U) ) (!  (=> (and (= (type d@@22) DatatypeTypeType) (|$IsA#_module.Node| d@@22)) (_module.Node.Node_q d@@22))
 :qid |unknown.0:0|
 :skolemid |960|
 :pattern ( (|$IsA#_module.Node| d@@22))
)))
(assert (forall ((_module.Node$A@@7 T@U) (d@@23 T@U) ) (!  (=> (and (and (= (type _module.Node$A@@7) TyType) (= (type d@@23) DatatypeTypeType)) ($Is d@@23 (Tclass._module.Node _module.Node$A@@7))) (_module.Node.Node_q d@@23))
 :qid |unknown.0:0|
 :skolemid |961|
 :pattern ( (_module.Node.Node_q d@@23) ($Is d@@23 (Tclass._module.Node _module.Node$A@@7)))
)))
(assert (forall ((a@@116 T@U) (b@@65 T@U) ) (!  (=> (and (and (= (type a@@116) DatatypeTypeType) (= (type b@@65) DatatypeTypeType)) true) (and (=> (|_module.Node#Equal| a@@116 b@@65) (and (and (|_module.Option#Equal| (_module.Node.data a@@116) (_module.Node.data b@@65)) (= (_module.Node.next a@@116) (_module.Node.next b@@65))) (= (_module.Node.prev a@@116) (_module.Node.prev b@@65)))) (=> (and (and (|_module.Option#Equal| (_module.Node.data a@@116) (_module.Node.data b@@65)) (= (_module.Node.next a@@116) (_module.Node.next b@@65))) (= (_module.Node.prev a@@116) (_module.Node.prev b@@65))) (|_module.Node#Equal| a@@116 b@@65))))
 :qid |unknown.0:0|
 :skolemid |962|
 :pattern ( (|_module.Node#Equal| a@@116 b@@65))
)))
(assert (forall ((a@@117 T@U) (b@@66 T@U) ) (!  (=> (and (= (type a@@117) DatatypeTypeType) (= (type b@@66) DatatypeTypeType)) (and (=> (|_module.Node#Equal| a@@117 b@@66) (= a@@117 b@@66)) (=> (= a@@117 b@@66) (|_module.Node#Equal| a@@117 b@@66))))
 :qid |unknown.0:0|
 :skolemid |963|
 :pattern ( (|_module.Node#Equal| a@@117 b@@66))
)))
(assert (forall ((arg0@@233 T@U) (arg1@@107 Int) (arg2@@63 T@U) (arg3@@40 T@U) (arg4@@29 T@U) ) (! (= (type (|#_module.DList.DList| arg0@@233 arg1@@107 arg2@@63 arg3@@40 arg4@@29)) DatatypeTypeType)
 :qid |funType:#_module.DList.DList|
 :pattern ( (|#_module.DList.DList| arg0@@233 arg1@@107 arg2@@63 arg3@@40 arg4@@29))
)))
(assert (forall ((|a#35#0#0| T@U) (|a#35#1#0| Int) (|a#35#2#0| T@U) (|a#35#3#0| T@U) (|a#35#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#35#0#0|) (SeqType BoxType)) (= (type |a#35#2#0|) (SeqType BoxType))) (= (type |a#35#3#0|) (SeqType BoxType))) (= (type |a#35#4#0|) (SeqType BoxType))) (= (DatatypeCtorId (|#_module.DList.DList| |a#35#0#0| |a#35#1#0| |a#35#2#0| |a#35#3#0| |a#35#4#0|)) |##_module.DList.DList|))
 :qid |DLLDafny.77:3|
 :skolemid |964|
 :pattern ( (|#_module.DList.DList| |a#35#0#0| |a#35#1#0| |a#35#2#0| |a#35#3#0| |a#35#4#0|))
)))
(assert (forall ((d@@24 T@U) ) (!  (=> (= (type d@@24) DatatypeTypeType) (and (=> (_module.DList.DList_q d@@24) (= (DatatypeCtorId d@@24) |##_module.DList.DList|)) (=> (= (DatatypeCtorId d@@24) |##_module.DList.DList|) (_module.DList.DList_q d@@24))))
 :qid |unknown.0:0|
 :skolemid |965|
 :pattern ( (_module.DList.DList_q d@@24))
)))
(assert (forall ((d@@25 T@U) ) (!  (=> (and (= (type d@@25) DatatypeTypeType) (_module.DList.DList_q d@@25)) (exists ((|a#36#0#0| T@U) (|a#36#1#0| Int) (|a#36#2#0| T@U) (|a#36#3#0| T@U) (|a#36#4#0| T@U) ) (!  (and (and (and (and (= (type |a#36#0#0|) (SeqType BoxType)) (= (type |a#36#2#0|) (SeqType BoxType))) (= (type |a#36#3#0|) (SeqType BoxType))) (= (type |a#36#4#0|) (SeqType BoxType))) (= d@@25 (|#_module.DList.DList| |a#36#0#0| |a#36#1#0| |a#36#2#0| |a#36#3#0| |a#36#4#0|)))
 :qid |DLLDafny.77:3|
 :skolemid |966|
 :no-pattern (type |a#36#0#0|)
 :no-pattern (type |a#36#2#0|)
 :no-pattern (type |a#36#3#0|)
 :no-pattern (type |a#36#4#0|)
 :no-pattern (U_2_int |a#36#0#0|)
 :no-pattern (U_2_bool |a#36#0#0|)
 :no-pattern (U_2_int |a#36#2#0|)
 :no-pattern (U_2_bool |a#36#2#0|)
 :no-pattern (U_2_int |a#36#3#0|)
 :no-pattern (U_2_bool |a#36#3#0|)
 :no-pattern (U_2_int |a#36#4#0|)
 :no-pattern (U_2_bool |a#36#4#0|)
)))
 :qid |unknown.0:0|
 :skolemid |967|
 :pattern ( (_module.DList.DList_q d@@25))
)))
(assert (forall ((arg0@@234 T@U) ) (! (= (type (Tclass._module.DList arg0@@234)) TyType)
 :qid |funType:Tclass._module.DList|
 :pattern ( (Tclass._module.DList arg0@@234))
)))
(assert (forall ((_module.DList$A T@U) ) (!  (=> (= (type _module.DList$A) TyType) (= (Tag (Tclass._module.DList _module.DList$A)) Tagclass._module.DList))
 :qid |unknown.0:0|
 :skolemid |968|
 :pattern ( (Tclass._module.DList _module.DList$A))
)))
(assert (forall ((arg0@@235 T@U) ) (! (= (type (Tclass._module.DList_0 arg0@@235)) TyType)
 :qid |funType:Tclass._module.DList_0|
 :pattern ( (Tclass._module.DList_0 arg0@@235))
)))
(assert (forall ((_module.DList$A@@0 T@U) ) (!  (=> (= (type _module.DList$A@@0) TyType) (= (Tclass._module.DList_0 (Tclass._module.DList _module.DList$A@@0)) _module.DList$A@@0))
 :qid |unknown.0:0|
 :skolemid |969|
 :pattern ( (Tclass._module.DList _module.DList$A@@0))
)))
(assert (forall ((_module.DList$A@@1 T@U) (bx@@79 T@U) ) (!  (=> (and (and (= (type _module.DList$A@@1) TyType) (= (type bx@@79) BoxType)) ($IsBox bx@@79 (Tclass._module.DList _module.DList$A@@1))) (and (= ($Box ($Unbox DatatypeTypeType bx@@79)) bx@@79) ($Is ($Unbox DatatypeTypeType bx@@79) (Tclass._module.DList _module.DList$A@@1))))
 :qid |unknown.0:0|
 :skolemid |970|
 :pattern ( ($IsBox bx@@79 (Tclass._module.DList _module.DList$A@@1)))
)))
(assert (forall ((_module.DList$A@@2 T@U) (|a#37#0#0| T@U) (|a#37#1#0| Int) (|a#37#2#0| T@U) (|a#37#3#0| T@U) (|a#37#4#0| T@U) ) (!  (=> (and (and (and (and (= (type _module.DList$A@@2) TyType) (= (type |a#37#0#0|) (SeqType BoxType))) (= (type |a#37#2#0|) (SeqType BoxType))) (= (type |a#37#3#0|) (SeqType BoxType))) (= (type |a#37#4#0|) (SeqType BoxType))) (and (=> ($Is (|#_module.DList.DList| |a#37#0#0| |a#37#1#0| |a#37#2#0| |a#37#3#0| |a#37#4#0|) (Tclass._module.DList _module.DList$A@@2)) (and (and (and (and ($Is |a#37#0#0| (TSeq (Tclass._module.Node _module.DList$A@@2))) ($Is (int_2_U |a#37#1#0|) TInt)) ($Is |a#37#2#0| (TSeq _module.DList$A@@2))) ($Is |a#37#3#0| (TSeq TInt))) ($Is |a#37#4#0| (TSeq TInt)))) (=> (and (and (and (and ($Is |a#37#0#0| (TSeq (Tclass._module.Node _module.DList$A@@2))) ($Is (int_2_U |a#37#1#0|) TInt)) ($Is |a#37#2#0| (TSeq _module.DList$A@@2))) ($Is |a#37#3#0| (TSeq TInt))) ($Is |a#37#4#0| (TSeq TInt))) ($Is (|#_module.DList.DList| |a#37#0#0| |a#37#1#0| |a#37#2#0| |a#37#3#0| |a#37#4#0|) (Tclass._module.DList _module.DList$A@@2)))))
 :qid |unknown.0:0|
 :skolemid |971|
 :pattern ( ($Is (|#_module.DList.DList| |a#37#0#0| |a#37#1#0| |a#37#2#0| |a#37#3#0| |a#37#4#0|) (Tclass._module.DList _module.DList$A@@2)))
)))
(assert (forall ((_module.DList$A@@3 T@U) (|a#38#0#0| T@U) (|a#38#1#0| Int) (|a#38#2#0| T@U) (|a#38#3#0| T@U) (|a#38#4#0| T@U) ($h@@28 T@U) ) (!  (=> (and (and (and (and (and (and (= (type _module.DList$A@@3) TyType) (= (type |a#38#0#0|) (SeqType BoxType))) (= (type |a#38#2#0|) (SeqType BoxType))) (= (type |a#38#3#0|) (SeqType BoxType))) (= (type |a#38#4#0|) (SeqType BoxType))) (= (type $h@@28) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@28)) (and (=> ($IsAlloc (|#_module.DList.DList| |a#38#0#0| |a#38#1#0| |a#38#2#0| |a#38#3#0| |a#38#4#0|) (Tclass._module.DList _module.DList$A@@3) $h@@28) (and (and (and (and ($IsAlloc |a#38#0#0| (TSeq (Tclass._module.Node _module.DList$A@@3)) $h@@28) ($IsAlloc (int_2_U |a#38#1#0|) TInt $h@@28)) ($IsAlloc |a#38#2#0| (TSeq _module.DList$A@@3) $h@@28)) ($IsAlloc |a#38#3#0| (TSeq TInt) $h@@28)) ($IsAlloc |a#38#4#0| (TSeq TInt) $h@@28))) (=> (and (and (and (and ($IsAlloc |a#38#0#0| (TSeq (Tclass._module.Node _module.DList$A@@3)) $h@@28) ($IsAlloc (int_2_U |a#38#1#0|) TInt $h@@28)) ($IsAlloc |a#38#2#0| (TSeq _module.DList$A@@3) $h@@28)) ($IsAlloc |a#38#3#0| (TSeq TInt) $h@@28)) ($IsAlloc |a#38#4#0| (TSeq TInt) $h@@28)) ($IsAlloc (|#_module.DList.DList| |a#38#0#0| |a#38#1#0| |a#38#2#0| |a#38#3#0| |a#38#4#0|) (Tclass._module.DList _module.DList$A@@3) $h@@28))))
 :qid |unknown.0:0|
 :skolemid |972|
 :pattern ( ($IsAlloc (|#_module.DList.DList| |a#38#0#0| |a#38#1#0| |a#38#2#0| |a#38#3#0| |a#38#4#0|) (Tclass._module.DList _module.DList$A@@3) $h@@28))
)))
(assert (forall ((arg0@@236 T@U) ) (! (= (type (_module.DList.nodes arg0@@236)) (SeqType BoxType))
 :qid |funType:_module.DList.nodes|
 :pattern ( (_module.DList.nodes arg0@@236))
)))
(assert (forall ((d@@26 T@U) (_module.DList$A@@4 T@U) ($h@@29 T@U) ) (!  (=> (and (and (and (= (type d@@26) DatatypeTypeType) (= (type _module.DList$A@@4) TyType)) (= (type $h@@29) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@29) (and (_module.DList.DList_q d@@26) ($IsAlloc d@@26 (Tclass._module.DList _module.DList$A@@4) $h@@29)))) ($IsAlloc (_module.DList.nodes d@@26) (TSeq (Tclass._module.Node _module.DList$A@@4)) $h@@29))
 :qid |unknown.0:0|
 :skolemid |973|
 :pattern ( ($IsAlloc (_module.DList.nodes d@@26) (TSeq (Tclass._module.Node _module.DList$A@@4)) $h@@29))
)))
(assert (forall ((d@@27 T@U) ($h@@30 T@U) ) (!  (=> (and (and (= (type d@@27) DatatypeTypeType) (= (type $h@@30) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@30) (and (_module.DList.DList_q d@@27) (exists ((_module.DList$A@@5 T@U) ) (!  (and (= (type _module.DList$A@@5) TyType) ($IsAlloc d@@27 (Tclass._module.DList _module.DList$A@@5) $h@@30))
 :qid |unknown.0:0|
 :skolemid |974|
 :pattern ( ($IsAlloc d@@27 (Tclass._module.DList _module.DList$A@@5) $h@@30))
))))) ($IsAlloc (int_2_U (_module.DList.freeStack d@@27)) TInt $h@@30))
 :qid |unknown.0:0|
 :skolemid |975|
 :pattern ( ($IsAlloc (int_2_U (_module.DList.freeStack d@@27)) TInt $h@@30))
)))
(assert (forall ((arg0@@237 T@U) ) (! (= (type (_module.DList.s arg0@@237)) (SeqType BoxType))
 :qid |funType:_module.DList.s|
 :pattern ( (_module.DList.s arg0@@237))
)))
(assert (forall ((d@@28 T@U) (_module.DList$A@@6 T@U) ($h@@31 T@U) ) (!  (=> (and (and (and (= (type d@@28) DatatypeTypeType) (= (type _module.DList$A@@6) TyType)) (= (type $h@@31) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@31) (and (_module.DList.DList_q d@@28) ($IsAlloc d@@28 (Tclass._module.DList _module.DList$A@@6) $h@@31)))) ($IsAlloc (_module.DList.s d@@28) (TSeq _module.DList$A@@6) $h@@31))
 :qid |unknown.0:0|
 :skolemid |976|
 :pattern ( ($IsAlloc (_module.DList.s d@@28) (TSeq _module.DList$A@@6) $h@@31))
)))
(assert (forall ((arg0@@238 T@U) ) (! (= (type (_module.DList.f arg0@@238)) (SeqType BoxType))
 :qid |funType:_module.DList.f|
 :pattern ( (_module.DList.f arg0@@238))
)))
(assert (forall ((d@@29 T@U) ($h@@32 T@U) ) (!  (=> (and (and (= (type d@@29) DatatypeTypeType) (= (type $h@@32) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@32) (and (_module.DList.DList_q d@@29) (exists ((_module.DList$A@@7 T@U) ) (!  (and (= (type _module.DList$A@@7) TyType) ($IsAlloc d@@29 (Tclass._module.DList _module.DList$A@@7) $h@@32))
 :qid |unknown.0:0|
 :skolemid |977|
 :pattern ( ($IsAlloc d@@29 (Tclass._module.DList _module.DList$A@@7) $h@@32))
))))) ($IsAlloc (_module.DList.f d@@29) (TSeq TInt) $h@@32))
 :qid |unknown.0:0|
 :skolemid |978|
 :pattern ( ($IsAlloc (_module.DList.f d@@29) (TSeq TInt) $h@@32))
)))
(assert (forall ((arg0@@239 T@U) ) (! (= (type (_module.DList.g arg0@@239)) (SeqType BoxType))
 :qid |funType:_module.DList.g|
 :pattern ( (_module.DList.g arg0@@239))
)))
(assert (forall ((d@@30 T@U) ($h@@33 T@U) ) (!  (=> (and (and (= (type d@@30) DatatypeTypeType) (= (type $h@@33) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@33) (and (_module.DList.DList_q d@@30) (exists ((_module.DList$A@@8 T@U) ) (!  (and (= (type _module.DList$A@@8) TyType) ($IsAlloc d@@30 (Tclass._module.DList _module.DList$A@@8) $h@@33))
 :qid |unknown.0:0|
 :skolemid |979|
 :pattern ( ($IsAlloc d@@30 (Tclass._module.DList _module.DList$A@@8) $h@@33))
))))) ($IsAlloc (_module.DList.g d@@30) (TSeq TInt) $h@@33))
 :qid |unknown.0:0|
 :skolemid |980|
 :pattern ( ($IsAlloc (_module.DList.g d@@30) (TSeq TInt) $h@@33))
)))
(assert (forall ((|a#39#0#0| T@U) (|a#39#1#0| Int) (|a#39#2#0| T@U) (|a#39#3#0| T@U) (|a#39#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#39#0#0|) (SeqType BoxType)) (= (type |a#39#2#0|) (SeqType BoxType))) (= (type |a#39#3#0|) (SeqType BoxType))) (= (type |a#39#4#0|) (SeqType BoxType))) (= (|#_module.DList.DList| (Lit |a#39#0#0|) |a#39#1#0| (Lit |a#39#2#0|) (Lit |a#39#3#0|) (Lit |a#39#4#0|)) (Lit (|#_module.DList.DList| |a#39#0#0| |a#39#1#0| |a#39#2#0| |a#39#3#0| |a#39#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |981|
 :pattern ( (|#_module.DList.DList| (Lit |a#39#0#0|) |a#39#1#0| (Lit |a#39#2#0|) (Lit |a#39#3#0|) (Lit |a#39#4#0|)))
)))
(assert (forall ((|a#40#0#0| T@U) (|a#40#1#0| Int) (|a#40#2#0| T@U) (|a#40#3#0| T@U) (|a#40#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#40#0#0|) (SeqType BoxType)) (= (type |a#40#2#0|) (SeqType BoxType))) (= (type |a#40#3#0|) (SeqType BoxType))) (= (type |a#40#4#0|) (SeqType BoxType))) (= (_module.DList.nodes (|#_module.DList.DList| |a#40#0#0| |a#40#1#0| |a#40#2#0| |a#40#3#0| |a#40#4#0|)) |a#40#0#0|))
 :qid |DLLDafny.77:3|
 :skolemid |982|
 :pattern ( (|#_module.DList.DList| |a#40#0#0| |a#40#1#0| |a#40#2#0| |a#40#3#0| |a#40#4#0|))
)))
(assert (forall ((|a#41#0#0| T@U) (|a#41#1#0| Int) (|a#41#2#0| T@U) (|a#41#3#0| T@U) (|a#41#4#0| T@U) (i@@31 Int) ) (!  (=> (and (and (and (and (= (type |a#41#0#0|) (SeqType BoxType)) (= (type |a#41#2#0|) (SeqType BoxType))) (= (type |a#41#3#0|) (SeqType BoxType))) (= (type |a#41#4#0|) (SeqType BoxType))) (and (<= 0 i@@31) (< i@@31 (|Seq#Length| |a#41#0#0|)))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| |a#41#0#0| i@@31))) (DtRank (|#_module.DList.DList| |a#41#0#0| |a#41#1#0| |a#41#2#0| |a#41#3#0| |a#41#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |983|
 :pattern ( (|Seq#Index| |a#41#0#0| i@@31) (|#_module.DList.DList| |a#41#0#0| |a#41#1#0| |a#41#2#0| |a#41#3#0| |a#41#4#0|))
)))
(assert (forall ((|a#42#0#0| T@U) (|a#42#1#0| Int) (|a#42#2#0| T@U) (|a#42#3#0| T@U) (|a#42#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#42#0#0|) (SeqType BoxType)) (= (type |a#42#2#0|) (SeqType BoxType))) (= (type |a#42#3#0|) (SeqType BoxType))) (= (type |a#42#4#0|) (SeqType BoxType))) (< (|Seq#Rank| |a#42#0#0|) (DtRank (|#_module.DList.DList| |a#42#0#0| |a#42#1#0| |a#42#2#0| |a#42#3#0| |a#42#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |984|
 :pattern ( (|#_module.DList.DList| |a#42#0#0| |a#42#1#0| |a#42#2#0| |a#42#3#0| |a#42#4#0|))
)))
(assert (forall ((|a#43#0#0| T@U) (|a#43#1#0| Int) (|a#43#2#0| T@U) (|a#43#3#0| T@U) (|a#43#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#43#0#0|) (SeqType BoxType)) (= (type |a#43#2#0|) (SeqType BoxType))) (= (type |a#43#3#0|) (SeqType BoxType))) (= (type |a#43#4#0|) (SeqType BoxType))) (= (_module.DList.freeStack (|#_module.DList.DList| |a#43#0#0| |a#43#1#0| |a#43#2#0| |a#43#3#0| |a#43#4#0|)) |a#43#1#0|))
 :qid |DLLDafny.77:3|
 :skolemid |985|
 :pattern ( (|#_module.DList.DList| |a#43#0#0| |a#43#1#0| |a#43#2#0| |a#43#3#0| |a#43#4#0|))
)))
(assert (forall ((|a#44#0#0| T@U) (|a#44#1#0| Int) (|a#44#2#0| T@U) (|a#44#3#0| T@U) (|a#44#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#44#0#0|) (SeqType BoxType)) (= (type |a#44#2#0|) (SeqType BoxType))) (= (type |a#44#3#0|) (SeqType BoxType))) (= (type |a#44#4#0|) (SeqType BoxType))) (= (_module.DList.s (|#_module.DList.DList| |a#44#0#0| |a#44#1#0| |a#44#2#0| |a#44#3#0| |a#44#4#0|)) |a#44#2#0|))
 :qid |DLLDafny.77:3|
 :skolemid |986|
 :pattern ( (|#_module.DList.DList| |a#44#0#0| |a#44#1#0| |a#44#2#0| |a#44#3#0| |a#44#4#0|))
)))
(assert (forall ((|a#45#0#0| T@U) (|a#45#1#0| Int) (|a#45#2#0| T@U) (|a#45#3#0| T@U) (|a#45#4#0| T@U) (i@@32 Int) ) (!  (=> (and (and (and (and (= (type |a#45#0#0|) (SeqType BoxType)) (= (type |a#45#2#0|) (SeqType BoxType))) (= (type |a#45#3#0|) (SeqType BoxType))) (= (type |a#45#4#0|) (SeqType BoxType))) (and (<= 0 i@@32) (< i@@32 (|Seq#Length| |a#45#2#0|)))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| |a#45#2#0| i@@32))) (DtRank (|#_module.DList.DList| |a#45#0#0| |a#45#1#0| |a#45#2#0| |a#45#3#0| |a#45#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |987|
 :pattern ( (|Seq#Index| |a#45#2#0| i@@32) (|#_module.DList.DList| |a#45#0#0| |a#45#1#0| |a#45#2#0| |a#45#3#0| |a#45#4#0|))
)))
(assert (forall ((|a#46#0#0| T@U) (|a#46#1#0| Int) (|a#46#2#0| T@U) (|a#46#3#0| T@U) (|a#46#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#46#0#0|) (SeqType BoxType)) (= (type |a#46#2#0|) (SeqType BoxType))) (= (type |a#46#3#0|) (SeqType BoxType))) (= (type |a#46#4#0|) (SeqType BoxType))) (< (|Seq#Rank| |a#46#2#0|) (DtRank (|#_module.DList.DList| |a#46#0#0| |a#46#1#0| |a#46#2#0| |a#46#3#0| |a#46#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |988|
 :pattern ( (|#_module.DList.DList| |a#46#0#0| |a#46#1#0| |a#46#2#0| |a#46#3#0| |a#46#4#0|))
)))
(assert (forall ((|a#47#0#0| T@U) (|a#47#1#0| Int) (|a#47#2#0| T@U) (|a#47#3#0| T@U) (|a#47#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#47#0#0|) (SeqType BoxType)) (= (type |a#47#2#0|) (SeqType BoxType))) (= (type |a#47#3#0|) (SeqType BoxType))) (= (type |a#47#4#0|) (SeqType BoxType))) (= (_module.DList.f (|#_module.DList.DList| |a#47#0#0| |a#47#1#0| |a#47#2#0| |a#47#3#0| |a#47#4#0|)) |a#47#3#0|))
 :qid |DLLDafny.77:3|
 :skolemid |989|
 :pattern ( (|#_module.DList.DList| |a#47#0#0| |a#47#1#0| |a#47#2#0| |a#47#3#0| |a#47#4#0|))
)))
(assert (forall ((|a#48#0#0| T@U) (|a#48#1#0| Int) (|a#48#2#0| T@U) (|a#48#3#0| T@U) (|a#48#4#0| T@U) (i@@33 Int) ) (!  (=> (and (and (and (and (= (type |a#48#0#0|) (SeqType BoxType)) (= (type |a#48#2#0|) (SeqType BoxType))) (= (type |a#48#3#0|) (SeqType BoxType))) (= (type |a#48#4#0|) (SeqType BoxType))) (and (<= 0 i@@33) (< i@@33 (|Seq#Length| |a#48#3#0|)))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| |a#48#3#0| i@@33))) (DtRank (|#_module.DList.DList| |a#48#0#0| |a#48#1#0| |a#48#2#0| |a#48#3#0| |a#48#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |990|
 :pattern ( (|Seq#Index| |a#48#3#0| i@@33) (|#_module.DList.DList| |a#48#0#0| |a#48#1#0| |a#48#2#0| |a#48#3#0| |a#48#4#0|))
)))
(assert (forall ((|a#49#0#0| T@U) (|a#49#1#0| Int) (|a#49#2#0| T@U) (|a#49#3#0| T@U) (|a#49#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#49#0#0|) (SeqType BoxType)) (= (type |a#49#2#0|) (SeqType BoxType))) (= (type |a#49#3#0|) (SeqType BoxType))) (= (type |a#49#4#0|) (SeqType BoxType))) (< (|Seq#Rank| |a#49#3#0|) (DtRank (|#_module.DList.DList| |a#49#0#0| |a#49#1#0| |a#49#2#0| |a#49#3#0| |a#49#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |991|
 :pattern ( (|#_module.DList.DList| |a#49#0#0| |a#49#1#0| |a#49#2#0| |a#49#3#0| |a#49#4#0|))
)))
(assert (forall ((|a#50#0#0| T@U) (|a#50#1#0| Int) (|a#50#2#0| T@U) (|a#50#3#0| T@U) (|a#50#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#50#0#0|) (SeqType BoxType)) (= (type |a#50#2#0|) (SeqType BoxType))) (= (type |a#50#3#0|) (SeqType BoxType))) (= (type |a#50#4#0|) (SeqType BoxType))) (= (_module.DList.g (|#_module.DList.DList| |a#50#0#0| |a#50#1#0| |a#50#2#0| |a#50#3#0| |a#50#4#0|)) |a#50#4#0|))
 :qid |DLLDafny.77:3|
 :skolemid |992|
 :pattern ( (|#_module.DList.DList| |a#50#0#0| |a#50#1#0| |a#50#2#0| |a#50#3#0| |a#50#4#0|))
)))
(assert (forall ((|a#51#0#0| T@U) (|a#51#1#0| Int) (|a#51#2#0| T@U) (|a#51#3#0| T@U) (|a#51#4#0| T@U) (i@@34 Int) ) (!  (=> (and (and (and (and (= (type |a#51#0#0|) (SeqType BoxType)) (= (type |a#51#2#0|) (SeqType BoxType))) (= (type |a#51#3#0|) (SeqType BoxType))) (= (type |a#51#4#0|) (SeqType BoxType))) (and (<= 0 i@@34) (< i@@34 (|Seq#Length| |a#51#4#0|)))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| |a#51#4#0| i@@34))) (DtRank (|#_module.DList.DList| |a#51#0#0| |a#51#1#0| |a#51#2#0| |a#51#3#0| |a#51#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |993|
 :pattern ( (|Seq#Index| |a#51#4#0| i@@34) (|#_module.DList.DList| |a#51#0#0| |a#51#1#0| |a#51#2#0| |a#51#3#0| |a#51#4#0|))
)))
(assert (forall ((|a#52#0#0| T@U) (|a#52#1#0| Int) (|a#52#2#0| T@U) (|a#52#3#0| T@U) (|a#52#4#0| T@U) ) (!  (=> (and (and (and (= (type |a#52#0#0|) (SeqType BoxType)) (= (type |a#52#2#0|) (SeqType BoxType))) (= (type |a#52#3#0|) (SeqType BoxType))) (= (type |a#52#4#0|) (SeqType BoxType))) (< (|Seq#Rank| |a#52#4#0|) (DtRank (|#_module.DList.DList| |a#52#0#0| |a#52#1#0| |a#52#2#0| |a#52#3#0| |a#52#4#0|))))
 :qid |DLLDafny.77:3|
 :skolemid |994|
 :pattern ( (|#_module.DList.DList| |a#52#0#0| |a#52#1#0| |a#52#2#0| |a#52#3#0| |a#52#4#0|))
)))
(assert (forall ((d@@31 T@U) ) (!  (=> (and (= (type d@@31) DatatypeTypeType) (|$IsA#_module.DList| d@@31)) (_module.DList.DList_q d@@31))
 :qid |unknown.0:0|
 :skolemid |995|
 :pattern ( (|$IsA#_module.DList| d@@31))
)))
(assert (forall ((_module.DList$A@@9 T@U) (d@@32 T@U) ) (!  (=> (and (and (= (type _module.DList$A@@9) TyType) (= (type d@@32) DatatypeTypeType)) ($Is d@@32 (Tclass._module.DList _module.DList$A@@9))) (_module.DList.DList_q d@@32))
 :qid |unknown.0:0|
 :skolemid |996|
 :pattern ( (_module.DList.DList_q d@@32) ($Is d@@32 (Tclass._module.DList _module.DList$A@@9)))
)))
(assert (forall ((a@@118 T@U) (b@@67 T@U) ) (!  (=> (and (and (= (type a@@118) DatatypeTypeType) (= (type b@@67) DatatypeTypeType)) true) (and (=> (|_module.DList#Equal| a@@118 b@@67) (and (and (and (and (|Seq#Equal| (_module.DList.nodes a@@118) (_module.DList.nodes b@@67)) (= (_module.DList.freeStack a@@118) (_module.DList.freeStack b@@67))) (|Seq#Equal| (_module.DList.s a@@118) (_module.DList.s b@@67))) (|Seq#Equal| (_module.DList.f a@@118) (_module.DList.f b@@67))) (|Seq#Equal| (_module.DList.g a@@118) (_module.DList.g b@@67)))) (=> (and (and (and (and (|Seq#Equal| (_module.DList.nodes a@@118) (_module.DList.nodes b@@67)) (= (_module.DList.freeStack a@@118) (_module.DList.freeStack b@@67))) (|Seq#Equal| (_module.DList.s a@@118) (_module.DList.s b@@67))) (|Seq#Equal| (_module.DList.f a@@118) (_module.DList.f b@@67))) (|Seq#Equal| (_module.DList.g a@@118) (_module.DList.g b@@67))) (|_module.DList#Equal| a@@118 b@@67))))
 :qid |unknown.0:0|
 :skolemid |997|
 :pattern ( (|_module.DList#Equal| a@@118 b@@67))
)))
(assert (forall ((a@@119 T@U) (b@@68 T@U) ) (!  (=> (and (= (type a@@119) DatatypeTypeType) (= (type b@@68) DatatypeTypeType)) (and (=> (|_module.DList#Equal| a@@119 b@@68) (= a@@119 b@@68)) (=> (= a@@119 b@@68) (|_module.DList#Equal| a@@119 b@@68))))
 :qid |unknown.0:0|
 :skolemid |998|
 :pattern ( (|_module.DList#Equal| a@@119 b@@68))
)))
(assert (= (type Tclass._module.__default) TyType))
(assert (= (Tag Tclass._module.__default) Tagclass._module.__default))
(assert (forall ((bx@@80 T@U) ) (!  (=> (and (= (type bx@@80) BoxType) ($IsBox bx@@80 Tclass._module.__default)) (and (= ($Box ($Unbox refType bx@@80)) bx@@80) ($Is ($Unbox refType bx@@80) Tclass._module.__default)))
 :qid |unknown.0:0|
 :skolemid |999|
 :pattern ( ($IsBox bx@@80 Tclass._module.__default))
)))
(assert (forall (($o@@7 T@U) ) (!  (=> (= (type $o@@7) refType) (and (=> ($Is $o@@7 Tclass._module.__default) (or (= $o@@7 null) (= (dtype $o@@7) Tclass._module.__default))) (=> (or (= $o@@7 null) (= (dtype $o@@7) Tclass._module.__default)) ($Is $o@@7 Tclass._module.__default))))
 :qid |unknown.0:0|
 :skolemid |1000|
 :pattern ( ($Is $o@@7 Tclass._module.__default))
)))
(assert (forall (($o@@8 T@U) ($h@@34 T@U) ) (!  (=> (and (= (type $o@@8) refType) (= (type $h@@34) (MapType0Type refType MapType1Type))) (and (=> ($IsAlloc $o@@8 Tclass._module.__default $h@@34) (or (= $o@@8 null) (U_2_bool (MapType1Select (MapType0Select $h@@34 $o@@8) alloc)))) (=> (or (= $o@@8 null) (U_2_bool (MapType1Select (MapType0Select $h@@34 $o@@8) alloc))) ($IsAlloc $o@@8 Tclass._module.__default $h@@34))))
 :qid |unknown.0:0|
 :skolemid |1001|
 :pattern ( ($IsAlloc $o@@8 Tclass._module.__default $h@@34))
)))
(assert  (=> (<= 23 $FunctionContextHeight) (forall ((|a#0| Int) (|b#0| Int) ) (!  (=> (or (|_module.__default.Dec#canCall| |a#0| |b#0|) (not (= 23 $FunctionContextHeight))) true)
 :qid |DLLDafny.1:21|
 :skolemid |1002|
 :pattern ( (_module.__default.Dec |a#0| |b#0|))
))))
(assert (forall ((|a#0@@0| Int) (|b#0@@0| Int) ) (!  (and (=> (|_module.__default.Dec#requires| |a#0@@0| |b#0@@0|) true) (=> true (|_module.__default.Dec#requires| |a#0@@0| |b#0@@0|)))
 :qid |DLLDafny.1:21|
 :skolemid |1003|
 :pattern ( (|_module.__default.Dec#requires| |a#0@@0| |b#0@@0|))
)))
(assert  (=> (<= 9 $FunctionContextHeight) (forall ((|a#0@@1| Int) (|b#0@@1| Int) ) (!  (=> (or (|_module.__default.Add#canCall| |a#0@@1| |b#0@@1|) (not (= 9 $FunctionContextHeight))) true)
 :qid |DLLDafny.8:21|
 :skolemid |1007|
 :pattern ( (_module.__default.Add |a#0@@1| |b#0@@1|))
))))
(assert (forall ((|a#0@@2| Int) (|b#0@@2| Int) ) (!  (and (=> (|_module.__default.Add#requires| |a#0@@2| |b#0@@2|) true) (=> true (|_module.__default.Add#requires| |a#0@@2| |b#0@@2|)))
 :qid |DLLDafny.8:21|
 :skolemid |1008|
 :pattern ( (|_module.__default.Add#requires| |a#0@@2| |b#0@@2|))
)))
(assert  (=> (<= 9 $FunctionContextHeight) (forall ((|a#0@@3| Int) (|b#0@@3| Int) ) (!  (=> (or (|_module.__default.Add#canCall| |a#0@@3| |b#0@@3|) (not (= 9 $FunctionContextHeight))) (= (_module.__default.Add |a#0@@3| |b#0@@3|) (+ |a#0@@3| |b#0@@3|)))
 :qid |DLLDafny.8:21|
 :skolemid |1009|
 :pattern ( (_module.__default.Add |a#0@@3| |b#0@@3|))
))))
(assert  (=> (<= 9 $FunctionContextHeight) (forall ((|a#0@@4| Int) (|b#0@@4| Int) ) (!  (=> (or (|_module.__default.Add#canCall| |a#0@@4| |b#0@@4|) (not (= 9 $FunctionContextHeight))) (= (_module.__default.Add |a#0@@4| |b#0@@4|) (+ |a#0@@4| |b#0@@4|)))
 :qid |DLLDafny.8:21|
 :weight 3
 :skolemid |1010|
 :pattern ( (_module.__default.Add |a#0@@4| |b#0@@4|))
))))
(assert  (=> (<= 10 $FunctionContextHeight) (forall ((|a#0@@5| Int) (|b#0@@5| Int) ) (!  (=> (or (|_module.__default.Sub#canCall| |a#0@@5| |b#0@@5|) (not (= 10 $FunctionContextHeight))) true)
 :qid |DLLDafny.9:21|
 :skolemid |1011|
 :pattern ( (_module.__default.Sub |a#0@@5| |b#0@@5|))
))))
(assert (forall ((|a#0@@6| Int) (|b#0@@6| Int) ) (!  (and (=> (|_module.__default.Sub#requires| |a#0@@6| |b#0@@6|) true) (=> true (|_module.__default.Sub#requires| |a#0@@6| |b#0@@6|)))
 :qid |DLLDafny.9:21|
 :skolemid |1012|
 :pattern ( (|_module.__default.Sub#requires| |a#0@@6| |b#0@@6|))
)))
(assert  (=> (<= 10 $FunctionContextHeight) (forall ((|a#0@@7| Int) (|b#0@@7| Int) ) (!  (=> (or (|_module.__default.Sub#canCall| |a#0@@7| |b#0@@7|) (not (= 10 $FunctionContextHeight))) (= (_module.__default.Sub |a#0@@7| |b#0@@7|) (- |a#0@@7| |b#0@@7|)))
 :qid |DLLDafny.9:21|
 :skolemid |1013|
 :pattern ( (_module.__default.Sub |a#0@@7| |b#0@@7|))
))))
(assert  (=> (<= 10 $FunctionContextHeight) (forall ((|a#0@@8| Int) (|b#0@@8| Int) ) (!  (=> (or (|_module.__default.Sub#canCall| |a#0@@8| |b#0@@8|) (not (= 10 $FunctionContextHeight))) (= (_module.__default.Sub |a#0@@8| |b#0@@8|) (- |a#0@@8| |b#0@@8|)))
 :qid |DLLDafny.9:21|
 :weight 3
 :skolemid |1014|
 :pattern ( (_module.__default.Sub |a#0@@8| |b#0@@8|))
))))
(assert (forall ((arg0@@240 T@U) (arg1@@108 T@U) (arg2@@64 Int) ) (! (= (type (_module.__default.SeqRemove arg0@@240 arg1@@108 arg2@@64)) (SeqType BoxType))
 :qid |funType:_module.__default.SeqRemove|
 :pattern ( (_module.__default.SeqRemove arg0@@240 arg1@@108 arg2@@64))
)))
(assert  (=> (<= 35 $FunctionContextHeight) (forall ((_module._default.SeqRemove$X T@U) (|s#0| T@U) (|k#0| Int) ) (!  (=> (and (and (= (type _module._default.SeqRemove$X) TyType) (= (type |s#0|) (SeqType BoxType))) (or (|_module.__default.SeqRemove#canCall| _module._default.SeqRemove$X |s#0| |k#0|) (and (not (= 35 $FunctionContextHeight)) (and ($Is |s#0| (TSeq _module._default.SeqRemove$X)) (and (<= 0 |k#0|) (< |k#0| (|Seq#Length| |s#0|))))))) (and (and (= (_module.__default.Sub (|Seq#Length| |s#0|) 1) (|Seq#Length| (_module.__default.SeqRemove _module._default.SeqRemove$X |s#0| |k#0|))) (forall ((|i#0| Int) ) (!  (=> true (=> (and (<= 0 |i#0|) (< |i#0| (|Seq#Length| (_module.__default.SeqRemove _module._default.SeqRemove$X |s#0| |k#0|)))) (ite (< |i#0| |k#0|) (= (|Seq#Index| (_module.__default.SeqRemove _module._default.SeqRemove$X |s#0| |k#0|) |i#0|) (|Seq#Index| |s#0| |i#0|)) (= (|Seq#Index| (_module.__default.SeqRemove _module._default.SeqRemove$X |s#0| |k#0|) |i#0|) (|Seq#Index| |s#0| (_module.__default.Add |i#0| 1))))))
 :qid |DLLDafny.14:18|
 :skolemid |1015|
 :pattern ( (|Seq#Index| (_module.__default.SeqRemove _module._default.SeqRemove$X |s#0| |k#0|) |i#0|))
))) ($Is (_module.__default.SeqRemove _module._default.SeqRemove$X |s#0| |k#0|) (TSeq _module._default.SeqRemove$X))))
 :qid |unknown.0:0|
 :skolemid |1016|
 :pattern ( (_module.__default.SeqRemove _module._default.SeqRemove$X |s#0| |k#0|))
))))
(assert (forall ((_module._default.SeqRemove$X@@0 T@U) (|s#0@@0| T@U) (|k#0@@0| Int) ) (!  (=> (and (and (= (type _module._default.SeqRemove$X@@0) TyType) (= (type |s#0@@0|) (SeqType BoxType))) ($Is |s#0@@0| (TSeq _module._default.SeqRemove$X@@0))) (and (=> (|_module.__default.SeqRemove#requires| _module._default.SeqRemove$X@@0 |s#0@@0| |k#0@@0|) (and (<= 0 |k#0@@0|) (< |k#0@@0| (|Seq#Length| |s#0@@0|)))) (=> (and (<= 0 |k#0@@0|) (< |k#0@@0| (|Seq#Length| |s#0@@0|))) (|_module.__default.SeqRemove#requires| _module._default.SeqRemove$X@@0 |s#0@@0| |k#0@@0|))))
 :qid |unknown.0:0|
 :skolemid |1017|
 :pattern ( (|_module.__default.SeqRemove#requires| _module._default.SeqRemove$X@@0 |s#0@@0| |k#0@@0|))
)))
(assert (forall ((arg0@@241 T@U) (arg1@@109 T@U) (arg2@@65 Int) (arg3@@41 T@U) ) (! (= (type (_module.__default.SeqInsert arg0@@241 arg1@@109 arg2@@65 arg3@@41)) (SeqType BoxType))
 :qid |funType:_module.__default.SeqInsert|
 :pattern ( (_module.__default.SeqInsert arg0@@241 arg1@@109 arg2@@65 arg3@@41))
)))
(assert  (=> (<= 38 $FunctionContextHeight) (forall ((_module._default.SeqInsert$X T@U) (|s#0@@1| T@U) (|k#0@@1| Int) (|v#0| T@U) ) (!  (=> (and (and (and (= (type _module._default.SeqInsert$X) TyType) (= (type |s#0@@1|) (SeqType BoxType))) (= (type |v#0|) BoxType)) (or (|_module.__default.SeqInsert#canCall| _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|) (and (not (= 38 $FunctionContextHeight)) (and (and ($Is |s#0@@1| (TSeq _module._default.SeqInsert$X)) ($IsBox |v#0| _module._default.SeqInsert$X)) (and (<= 0 |k#0@@1|) (<= |k#0@@1| (|Seq#Length| |s#0@@1|))))))) (and (and (= (|Seq#Length| (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|)) (_module.__default.Add (|Seq#Length| |s#0@@1|) 1)) (forall ((|i#0@@0| Int) ) (!  (=> true (=> (and (<= 0 |i#0@@0|) (< |i#0@@0| (|Seq#Length| (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|)))) (ite (< |i#0@@0| |k#0@@1|) (= (|Seq#Index| (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|) |i#0@@0|) (|Seq#Index| |s#0@@1| |i#0@@0|)) (ite (= |i#0@@0| |k#0@@1|) (= (|Seq#Index| (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|) |i#0@@0|) |v#0|) (= (|Seq#Index| (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|) |i#0@@0|) (|Seq#Index| |s#0@@1| (_module.__default.Sub |i#0@@0| 1)))))))
 :qid |DLLDafny.21:18|
 :skolemid |1020|
 :pattern ( (|Seq#Index| (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|) |i#0@@0|))
))) ($Is (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|) (TSeq _module._default.SeqInsert$X))))
 :qid |unknown.0:0|
 :skolemid |1021|
 :pattern ( (_module.__default.SeqInsert _module._default.SeqInsert$X |s#0@@1| |k#0@@1| |v#0|))
))))
(assert (forall ((_module._default.SeqInsert$X@@0 T@U) (|s#0@@2| T@U) (|k#0@@2| Int) (|v#0@@0| T@U) ) (!  (=> (and (and (and (= (type _module._default.SeqInsert$X@@0) TyType) (= (type |s#0@@2|) (SeqType BoxType))) (= (type |v#0@@0|) BoxType)) (and ($Is |s#0@@2| (TSeq _module._default.SeqInsert$X@@0)) ($IsBox |v#0@@0| _module._default.SeqInsert$X@@0))) (and (=> (|_module.__default.SeqInsert#requires| _module._default.SeqInsert$X@@0 |s#0@@2| |k#0@@2| |v#0@@0|) (and (<= 0 |k#0@@2|) (<= |k#0@@2| (|Seq#Length| |s#0@@2|)))) (=> (and (<= 0 |k#0@@2|) (<= |k#0@@2| (|Seq#Length| |s#0@@2|))) (|_module.__default.SeqInsert#requires| _module._default.SeqInsert$X@@0 |s#0@@2| |k#0@@2| |v#0@@0|))))
 :qid |unknown.0:0|
 :skolemid |1022|
 :pattern ( (|_module.__default.SeqInsert#requires| _module._default.SeqInsert$X@@0 |s#0@@2| |k#0@@2| |v#0@@0|))
)))
(assert (forall ((arg0@@242 T@U) (arg1@@110 Int) (arg2@@66 T@U) ) (! (= (type (_module.__default.SeqInit arg0@@242 arg1@@110 arg2@@66)) (SeqType BoxType))
 :qid |funType:_module.__default.SeqInit|
 :pattern ( (_module.__default.SeqInit arg0@@242 arg1@@110 arg2@@66))
)))
(assert  (=> (<= 4 $FunctionContextHeight) (forall ((_module._default.SeqInit$X T@U) ($Heap T@U) (|len#0| Int) (|func#0| T@U) ) (!  (=> (and (and (and (= (type _module._default.SeqInit$X) TyType) (= (type $Heap) (MapType0Type refType MapType1Type))) (= (type |func#0|) HandleTypeType)) (or (|_module.__default.SeqInit#canCall| _module._default.SeqInit$X |len#0| |func#0|) (and (not (= 4 $FunctionContextHeight)) (and (and ($IsGoodHeap $Heap) ($Is |func#0| (Tclass._System.___hPartialFunc1 TInt _module._default.SeqInit$X))) (and (>= |len#0| 0) (forall ((|i#0@@1| Int) ) (!  (=> true (=> (and (<= 0 |i#0@@1|) (< |i#0@@1| |len#0|)) (Requires1 TInt _module._default.SeqInit$X $Heap |func#0| ($Box (int_2_U |i#0@@1|)))))
 :qid |DLLDafny.28:19|
 :skolemid |1025|
 :pattern ( (Requires1 TInt _module._default.SeqInit$X $Heap |func#0| ($Box (int_2_U |i#0@@1|))))
))))))) (and (and (= (|Seq#Length| (_module.__default.SeqInit _module._default.SeqInit$X |len#0| |func#0|)) |len#0|) (forall ((|i#1| Int) ) (!  (=> true (=> (and (<= 0 |i#1|) (< |i#1| |len#0|)) (= (|Seq#Index| (_module.__default.SeqInit _module._default.SeqInit$X |len#0| |func#0|) |i#1|) (Apply1 TInt _module._default.SeqInit$X $Heap |func#0| ($Box (int_2_U |i#1|))))))
 :qid |DLLDafny.30:18|
 :skolemid |1026|
 :pattern ( (|Seq#Index| (_module.__default.SeqInit _module._default.SeqInit$X |len#0| |func#0|) |i#1|))
))) ($Is (_module.__default.SeqInit _module._default.SeqInit$X |len#0| |func#0|) (TSeq _module._default.SeqInit$X))))
 :qid |unknown.0:0|
 :skolemid |1027|
 :pattern ( (_module.__default.SeqInit _module._default.SeqInit$X |len#0| |func#0|) ($IsGoodHeap $Heap))
))))
(assert (forall ((_module._default.SeqInit$X@@0 T@U) ($Heap@@0 T@U) (|len#0@@0| Int) (|func#0@@0| T@U) ) (!  (=> (and (and (and (= (type _module._default.SeqInit$X@@0) TyType) (= (type $Heap@@0) (MapType0Type refType MapType1Type))) (= (type |func#0@@0|) HandleTypeType)) (and ($IsGoodHeap $Heap@@0) ($Is |func#0@@0| (Tclass._System.___hPartialFunc1 TInt _module._default.SeqInit$X@@0)))) (and (=> (|_module.__default.SeqInit#requires| _module._default.SeqInit$X@@0 |len#0@@0| |func#0@@0|) (and (>= |len#0@@0| 0) (forall ((|i#2| T@U) ) (!  (=> (and (and (= (type |i#2|) intType) true) (and (<= 0 (U_2_int |i#2|)) (< (U_2_int |i#2|) |len#0@@0|))) (Requires1 TInt _module._default.SeqInit$X@@0 $Heap@@0 |func#0@@0| ($Box |i#2|)))
 :qid |DLLDafny.28:19|
 :skolemid |1028|
 :pattern ( (Requires1 TInt _module._default.SeqInit$X@@0 $Heap@@0 |func#0@@0| ($Box |i#2|)))
)))) (=> (and (>= |len#0@@0| 0) (forall ((|i#2@@0| Int) ) (!  (=> true (=> (and (<= 0 |i#2@@0|) (< |i#2@@0| |len#0@@0|)) (Requires1 TInt _module._default.SeqInit$X@@0 $Heap@@0 |func#0@@0| ($Box (int_2_U |i#2@@0|)))))
 :qid |DLLDafny.28:19|
 :skolemid |1028|
 :pattern ( (Requires1 TInt _module._default.SeqInit$X@@0 $Heap@@0 |func#0@@0| ($Box (int_2_U |i#2@@0|))))
))) (|_module.__default.SeqInit#requires| _module._default.SeqInit$X@@0 |len#0@@0| |func#0@@0|))))
 :qid |unknown.0:0|
 :skolemid |1029|
 :pattern ( (|_module.__default.SeqInit#requires| _module._default.SeqInit$X@@0 |len#0@@0| |func#0@@0|) ($IsGoodHeap $Heap@@0))
)))
(assert (forall ((arg0@@243 T@U) (arg1@@111 T@U) (arg2@@67 Int) ) (! (= (type (_module.__default.seq__get arg0@@243 arg1@@111 arg2@@67)) BoxType)
 :qid |funType:_module.__default.seq__get|
 :pattern ( (_module.__default.seq__get arg0@@243 arg1@@111 arg2@@67))
)))
(assert  (=> (<= 18 $FunctionContextHeight) (forall ((_module._default.seq_get$A T@U) (|s#0@@3| T@U) (|i#0@@2| Int) ) (!  (=> (and (and (= (type _module._default.seq_get$A) TyType) (= (type |s#0@@3|) (SeqType BoxType))) (or (|_module.__default.seq__get#canCall| _module._default.seq_get$A |s#0@@3| |i#0@@2|) (and (not (= 18 $FunctionContextHeight)) (and ($Is |s#0@@3| (TSeq _module._default.seq_get$A)) (and (<= 0 |i#0@@2|) (< |i#0@@2| (|Seq#Length| |s#0@@3|))))))) (and (= (_module.__default.seq__get _module._default.seq_get$A |s#0@@3| |i#0@@2|) (|Seq#Index| |s#0@@3| |i#0@@2|)) ($IsBox (_module.__default.seq__get _module._default.seq_get$A |s#0@@3| |i#0@@2|) _module._default.seq_get$A)))
 :qid |unknown.0:0|
 :skolemid |1034|
 :pattern ( (_module.__default.seq__get _module._default.seq_get$A |s#0@@3| |i#0@@2|))
))))
(assert (forall ((_module._default.seq_get$A@@0 T@U) (|s#0@@4| T@U) (|i#0@@3| Int) ) (!  (=> (and (and (= (type _module._default.seq_get$A@@0) TyType) (= (type |s#0@@4|) (SeqType BoxType))) ($Is |s#0@@4| (TSeq _module._default.seq_get$A@@0))) (and (=> (|_module.__default.seq__get#requires| _module._default.seq_get$A@@0 |s#0@@4| |i#0@@3|) (and (<= 0 |i#0@@3|) (< |i#0@@3| (|Seq#Length| |s#0@@4|)))) (=> (and (<= 0 |i#0@@3|) (< |i#0@@3| (|Seq#Length| |s#0@@4|))) (|_module.__default.seq__get#requires| _module._default.seq_get$A@@0 |s#0@@4| |i#0@@3|))))
 :qid |unknown.0:0|
 :skolemid |1035|
 :pattern ( (|_module.__default.seq__get#requires| _module._default.seq_get$A@@0 |s#0@@4| |i#0@@3|))
)))
(assert (forall ((arg0@@244 T@U) (arg1@@112 T@U) (arg2@@68 Int) (arg3@@42 T@U) ) (! (= (type (_module.__default.seq__set arg0@@244 arg1@@112 arg2@@68 arg3@@42)) (SeqType BoxType))
 :qid |funType:_module.__default.seq__set|
 :pattern ( (_module.__default.seq__set arg0@@244 arg1@@112 arg2@@68 arg3@@42))
)))
(assert  (=> (<= 24 $FunctionContextHeight) (forall ((_module._default.seq_set$A T@U) (|s1#0| T@U) (|i#0@@4| Int) (|a#0@@9| T@U) ) (!  (=> (and (and (and (= (type _module._default.seq_set$A) TyType) (= (type |s1#0|) (SeqType BoxType))) (= (type |a#0@@9|) BoxType)) (or (|_module.__default.seq__set#canCall| _module._default.seq_set$A |s1#0| |i#0@@4| |a#0@@9|) (and (not (= 24 $FunctionContextHeight)) (and (and ($Is |s1#0| (TSeq _module._default.seq_set$A)) ($IsBox |a#0@@9| _module._default.seq_set$A)) (and (<= 0 |i#0@@4|) (< |i#0@@4| (|Seq#Length| |s1#0|))))))) (and (|Seq#Equal| (_module.__default.seq__set _module._default.seq_set$A |s1#0| |i#0@@4| |a#0@@9|) (|Seq#Update| |s1#0| |i#0@@4| |a#0@@9|)) ($Is (_module.__default.seq__set _module._default.seq_set$A |s1#0| |i#0@@4| |a#0@@9|) (TSeq _module._default.seq_set$A))))
 :qid |unknown.0:0|
 :skolemid |1036|
 :pattern ( (_module.__default.seq__set _module._default.seq_set$A |s1#0| |i#0@@4| |a#0@@9|))
))))
(assert (forall ((_module._default.seq_set$A@@0 T@U) (|s1#0@@0| T@U) (|i#0@@5| Int) (|a#0@@10| T@U) ) (!  (=> (and (and (and (= (type _module._default.seq_set$A@@0) TyType) (= (type |s1#0@@0|) (SeqType BoxType))) (= (type |a#0@@10|) BoxType)) (and ($Is |s1#0@@0| (TSeq _module._default.seq_set$A@@0)) ($IsBox |a#0@@10| _module._default.seq_set$A@@0))) (and (=> (|_module.__default.seq__set#requires| _module._default.seq_set$A@@0 |s1#0@@0| |i#0@@5| |a#0@@10|) (and (<= 0 |i#0@@5|) (< |i#0@@5| (|Seq#Length| |s1#0@@0|)))) (=> (and (<= 0 |i#0@@5|) (< |i#0@@5| (|Seq#Length| |s1#0@@0|))) (|_module.__default.seq__set#requires| _module._default.seq_set$A@@0 |s1#0@@0| |i#0@@5| |a#0@@10|))))
 :qid |unknown.0:0|
 :skolemid |1037|
 :pattern ( (|_module.__default.seq__set#requires| _module._default.seq_set$A@@0 |s1#0@@0| |i#0@@5| |a#0@@10|))
)))
(assert  (=> (<= 22 $FunctionContextHeight) (forall ((_module._default.seq_length$A T@U) (|s#0@@5| T@U) ) (!  (=> (and (and (= (type _module._default.seq_length$A) TyType) (= (type |s#0@@5|) (SeqType BoxType))) (or (|_module.__default.seq_length#canCall| _module._default.seq_length$A |s#0@@5|) (and (not (= 22 $FunctionContextHeight)) ($Is |s#0@@5| (TSeq _module._default.seq_length$A))))) (= (_module.__default.seq_length _module._default.seq_length$A |s#0@@5|) (|Seq#Length| |s#0@@5|)))
 :qid |unknown.0:0|
 :skolemid |1038|
 :pattern ( (_module.__default.seq_length _module._default.seq_length$A |s#0@@5|))
))))
(assert (forall ((_module._default.seq_length$A@@0 T@U) (|s#0@@6| T@U) ) (!  (=> (and (and (= (type _module._default.seq_length$A@@0) TyType) (= (type |s#0@@6|) (SeqType BoxType))) ($Is |s#0@@6| (TSeq _module._default.seq_length$A@@0))) (and (=> (|_module.__default.seq_length#requires| _module._default.seq_length$A@@0 |s#0@@6|) true) (=> true (|_module.__default.seq_length#requires| _module._default.seq_length$A@@0 |s#0@@6|))))
 :qid |unknown.0:0|
 :skolemid |1039|
 :pattern ( (|_module.__default.seq_length#requires| _module._default.seq_length$A@@0 |s#0@@6|))
)))
(assert (forall ((arg0@@245 T@U) ) (! (= (type (_module.__default.seq_empty arg0@@245)) (SeqType BoxType))
 :qid |funType:_module.__default.seq_empty|
 :pattern ( (_module.__default.seq_empty arg0@@245))
)))
(assert  (=> (<= 46 $FunctionContextHeight) (forall ((_module._default.seq_empty$A T@U) ) (!  (=> (and (= (type _module._default.seq_empty$A) TyType) (or (|_module.__default.seq_empty#canCall| _module._default.seq_empty$A) (not (= 46 $FunctionContextHeight)))) (and (= (|Seq#Length| (_module.__default.seq_empty _module._default.seq_empty$A)) 0) ($Is (_module.__default.seq_empty _module._default.seq_empty$A) (TSeq _module._default.seq_empty$A))))
 :qid |unknown.0:0|
 :skolemid |1040|
 :pattern ( (_module.__default.seq_empty _module._default.seq_empty$A))
))))
(assert (forall ((_module._default.seq_empty$A@@0 T@U) ) (!  (=> (= (type _module._default.seq_empty$A@@0) TyType) (and (=> (|_module.__default.seq_empty#requires| _module._default.seq_empty$A@@0) true) (=> true (|_module.__default.seq_empty#requires| _module._default.seq_empty$A@@0))))
 :qid |unknown.0:0|
 :skolemid |1041|
 :pattern ( (|_module.__default.seq_empty#requires| _module._default.seq_empty$A@@0))
)))
(assert (forall ((arg0@@246 T@U) (arg1@@113 Int) (arg2@@69 T@U) ) (! (= (type (_module.__default.seq_alloc arg0@@246 arg1@@113 arg2@@69)) (SeqType BoxType))
 :qid |funType:_module.__default.seq_alloc|
 :pattern ( (_module.__default.seq_alloc arg0@@246 arg1@@113 arg2@@69))
)))
(assert  (=> (<= 28 $FunctionContextHeight) (forall ((_module._default.seq_alloc$A T@U) (|length#0| Int) (|a#0@@11| T@U) ) (!  (=> (and (and (= (type _module._default.seq_alloc$A) TyType) (= (type |a#0@@11|) BoxType)) (or (|_module.__default.seq_alloc#canCall| _module._default.seq_alloc$A |length#0| |a#0@@11|) (and (not (= 28 $FunctionContextHeight)) ($IsBox |a#0@@11| _module._default.seq_alloc$A)))) (and (and (= (|Seq#Length| (_module.__default.seq_alloc _module._default.seq_alloc$A |length#0| |a#0@@11|)) |length#0|) (forall ((|i#0@@6| Int) ) (!  (=> true (=> (and (<= 0 |i#0@@6|) (< |i#0@@6| (|Seq#Length| (_module.__default.seq_alloc _module._default.seq_alloc$A |length#0| |a#0@@11|)))) (= (|Seq#Index| (_module.__default.seq_alloc _module._default.seq_alloc$A |length#0| |a#0@@11|) |i#0@@6|) |a#0@@11|)))
 :qid |DLLDafny.50:18|
 :skolemid |1042|
 :pattern ( (|Seq#Index| (_module.__default.seq_alloc _module._default.seq_alloc$A |length#0| |a#0@@11|) |i#0@@6|))
))) ($Is (_module.__default.seq_alloc _module._default.seq_alloc$A |length#0| |a#0@@11|) (TSeq _module._default.seq_alloc$A))))
 :qid |unknown.0:0|
 :skolemid |1043|
 :pattern ( (_module.__default.seq_alloc _module._default.seq_alloc$A |length#0| |a#0@@11|))
))))
(assert (forall ((_module._default.seq_alloc$A@@0 T@U) (|length#0@@0| Int) (|a#0@@12| T@U) ) (!  (=> (and (and (= (type _module._default.seq_alloc$A@@0) TyType) (= (type |a#0@@12|) BoxType)) ($IsBox |a#0@@12| _module._default.seq_alloc$A@@0)) (and (=> (|_module.__default.seq_alloc#requires| _module._default.seq_alloc$A@@0 |length#0@@0| |a#0@@12|) true) (=> true (|_module.__default.seq_alloc#requires| _module._default.seq_alloc$A@@0 |length#0@@0| |a#0@@12|))))
 :qid |unknown.0:0|
 :skolemid |1044|
 :pattern ( (|_module.__default.seq_alloc#requires| _module._default.seq_alloc$A@@0 |length#0@@0| |a#0@@12|))
)))
(assert (forall ((arg0@@247 T@U) (arg1@@114 T@U) ) (! (= (type (_module.__default.seq_free arg0@@247 arg1@@114)) DatatypeTypeType)
 :qid |funType:_module.__default.seq_free|
 :pattern ( (_module.__default.seq_free arg0@@247 arg1@@114))
)))
(assert  (=> (<= 6 $FunctionContextHeight) (forall ((_module._default.seq_free$A T@U) (|s#0@@7| T@U) ) (!  (=> (and (and (= (type _module._default.seq_free$A) TyType) (= (type |s#0@@7|) (SeqType BoxType))) (or (|_module.__default.seq_free#canCall| _module._default.seq_free$A |s#0@@7|) (and (not (= 6 $FunctionContextHeight)) ($Is |s#0@@7| (TSeq _module._default.seq_free$A))))) ($Is (_module.__default.seq_free _module._default.seq_free$A |s#0@@7|) Tclass._System.Tuple0))
 :qid |unknown.0:0|
 :skolemid |1047|
 :pattern ( (_module.__default.seq_free _module._default.seq_free$A |s#0@@7|))
))))
(assert (forall ((_module._default.seq_free$A@@0 T@U) (|s#0@@8| T@U) ) (!  (=> (and (and (= (type _module._default.seq_free$A@@0) TyType) (= (type |s#0@@8|) (SeqType BoxType))) ($Is |s#0@@8| (TSeq _module._default.seq_free$A@@0))) (and (=> (|_module.__default.seq_free#requires| _module._default.seq_free$A@@0 |s#0@@8|) true) (=> true (|_module.__default.seq_free#requires| _module._default.seq_free$A@@0 |s#0@@8|))))
 :qid |unknown.0:0|
 :skolemid |1048|
 :pattern ( (|_module.__default.seq_free#requires| _module._default.seq_free$A@@0 |s#0@@8|))
)))
(assert (forall ((arg0@@248 T@U) (arg1@@115 T@U) ) (! (= (type (_module.__default.seq_unleash arg0@@248 arg1@@115)) (SeqType BoxType))
 :qid |funType:_module.__default.seq_unleash|
 :pattern ( (_module.__default.seq_unleash arg0@@248 arg1@@115))
)))
(assert  (=> (<= 47 $FunctionContextHeight) (forall ((_module._default.seq_unleash$A T@U) (|s1#0@@1| T@U) ) (!  (=> (and (and (= (type _module._default.seq_unleash$A) TyType) (= (type |s1#0@@1|) (SeqType BoxType))) (or (|_module.__default.seq_unleash#canCall| _module._default.seq_unleash$A |s1#0@@1|) (and (not (= 47 $FunctionContextHeight)) ($Is |s1#0@@1| (TSeq _module._default.seq_unleash$A))))) (and (|Seq#Equal| |s1#0@@1| (_module.__default.seq_unleash _module._default.seq_unleash$A |s1#0@@1|)) ($Is (_module.__default.seq_unleash _module._default.seq_unleash$A |s1#0@@1|) (TSeq _module._default.seq_unleash$A))))
 :qid |unknown.0:0|
 :skolemid |1049|
 :pattern ( (_module.__default.seq_unleash _module._default.seq_unleash$A |s1#0@@1|))
))))
(assert (forall ((_module._default.seq_unleash$A@@0 T@U) (|s1#0@@2| T@U) ) (!  (=> (and (and (= (type _module._default.seq_unleash$A@@0) TyType) (= (type |s1#0@@2|) (SeqType BoxType))) ($Is |s1#0@@2| (TSeq _module._default.seq_unleash$A@@0))) (and (=> (|_module.__default.seq_unleash#requires| _module._default.seq_unleash$A@@0 |s1#0@@2|) true) (=> true (|_module.__default.seq_unleash#requires| _module._default.seq_unleash$A@@0 |s1#0@@2|))))
 :qid |unknown.0:0|
 :skolemid |1050|
 :pattern ( (|_module.__default.seq_unleash#requires| _module._default.seq_unleash$A@@0 |s1#0@@2|))
)))
(assert  (=> (< 8 $FunctionContextHeight) ($Is (int_2_U (- 0 2)) TInt)))
(assert  (=> (< 8 $FunctionContextHeight) (forall (($h@@35 T@U) ) (!  (=> (and (= (type $h@@35) (MapType0Type refType MapType1Type)) ($IsGoodHeap $h@@35)) ($IsAlloc (int_2_U (- 0 2)) TInt $h@@35))
 :qid |DafnyPre.515:12|
 :skolemid |1057|
 :pattern ( ($IsAlloc (int_2_U (- 0 2)) TInt $h@@35))
))))
(assert  (=> (< 7 $FunctionContextHeight) ($Is (int_2_U (- 0 1)) TInt)))
(assert  (=> (< 7 $FunctionContextHeight) (forall (($h@@36 T@U) ) (!  (=> (and (= (type $h@@36) (MapType0Type refType MapType1Type)) ($IsGoodHeap $h@@36)) ($IsAlloc (int_2_U (- 0 1)) TInt $h@@36))
 :qid |DafnyPre.515:12|
 :skolemid |1058|
 :pattern ( ($IsAlloc (int_2_U (- 0 1)) TInt $h@@36))
))))
(assert  (=> (<= 11 $FunctionContextHeight) (forall ((_module._default.Invs$A T@U) (|nodes#0| T@U) (|freeStack#0| Int) (|s#0@@9| T@U) (|f#0@@19| T@U) (|g#0| T@U) ) (!  (=> (and (and (and (and (and (= (type _module._default.Invs$A) TyType) (= (type |nodes#0|) (SeqType BoxType))) (= (type |s#0@@9|) (SeqType BoxType))) (= (type |f#0@@19|) (SeqType BoxType))) (= (type |g#0|) (SeqType BoxType))) (or (|_module.__default.Invs#canCall| _module._default.Invs$A |nodes#0| |freeStack#0| |s#0@@9| |f#0@@19| |g#0|) (and (not (= 11 $FunctionContextHeight)) (and (and (and ($Is |nodes#0| (TSeq (Tclass._module.Node _module._default.Invs$A))) ($Is |s#0@@9| (TSeq _module._default.Invs$A))) ($Is |f#0@@19| (TSeq TInt))) ($Is |g#0| (TSeq TInt)))))) true)
 :qid |unknown.0:0|
 :skolemid |1059|
 :pattern ( (_module.__default.Invs _module._default.Invs$A |nodes#0| |freeStack#0| |s#0@@9| |f#0@@19| |g#0|))
))))
(assert (forall ((_module._default.Invs$A@@0 T@U) (|nodes#0@@0| T@U) (|freeStack#0@@0| Int) (|s#0@@10| T@U) (|f#0@@20| T@U) (|g#0@@0| T@U) ) (!  (=> (and (and (and (and (and (= (type _module._default.Invs$A@@0) TyType) (= (type |nodes#0@@0|) (SeqType BoxType))) (= (type |s#0@@10|) (SeqType BoxType))) (= (type |f#0@@20|) (SeqType BoxType))) (= (type |g#0@@0|) (SeqType BoxType))) (and (and (and ($Is |nodes#0@@0| (TSeq (Tclass._module.Node _module._default.Invs$A@@0))) ($Is |s#0@@10| (TSeq _module._default.Invs$A@@0))) ($Is |f#0@@20| (TSeq TInt))) ($Is |g#0@@0| (TSeq TInt)))) (and (=> (|_module.__default.Invs#requires| _module._default.Invs$A@@0 |nodes#0@@0| |freeStack#0@@0| |s#0@@10| |f#0@@20| |g#0@@0|) true) (=> true (|_module.__default.Invs#requires| _module._default.Invs$A@@0 |nodes#0@@0| |freeStack#0@@0| |s#0@@10| |f#0@@20| |g#0@@0|))))
 :qid |unknown.0:0|
 :skolemid |1060|
 :pattern ( (|_module.__default.Invs#requires| _module._default.Invs$A@@0 |nodes#0@@0| |freeStack#0@@0| |s#0@@10| |f#0@@20| |g#0@@0|))
)))
(assert  (=> (<= 11 $FunctionContextHeight) (forall ((_module._default.Invs$A@@1 T@U) (|nodes#0@@1| T@U) (|freeStack#0@@1| Int) (|s#0@@11| T@U) (|f#0@@21| T@U) (|g#0@@1| T@U) ) (!  (=> (and (and (and (and (and (= (type _module._default.Invs$A@@1) TyType) (= (type |nodes#0@@1|) (SeqType BoxType))) (= (type |s#0@@11|) (SeqType BoxType))) (= (type |f#0@@21|) (SeqType BoxType))) (= (type |g#0@@1|) (SeqType BoxType))) (or (|_module.__default.Invs#canCall| _module._default.Invs$A@@1 |nodes#0@@1| |freeStack#0@@1| |s#0@@11| |f#0@@21| |g#0@@1|) (and (not (= 11 $FunctionContextHeight)) (and (and (and ($Is |nodes#0@@1| (TSeq (Tclass._module.Node _module._default.Invs$A@@1))) ($Is |s#0@@11| (TSeq _module._default.Invs$A@@1))) ($Is |f#0@@21| (TSeq TInt))) ($Is |g#0@@1| (TSeq TInt)))))) (and (=> (= (|Seq#Length| |f#0@@21|) (|Seq#Length| |s#0@@11|)) (=> (= (|Seq#Length| |g#0@@1|) (|Seq#Length| |nodes#0@@1|)) (=> (> (|Seq#Length| |nodes#0@@1|) 0) (=> (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| 0))) (- 0 1)) (=> (<= 0 |freeStack#0@@1|) (=> (< |freeStack#0@@1| (|Seq#Length| |nodes#0@@1|)) (=> (forall ((|i#0@@7| Int) ) (!  (=> true (and (=> (and (<= 0 |i#0@@7|) (< |i#0@@7| (|Seq#Length| |f#0@@21|))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@7|))))) (=> (and (<= 0 |i#0@@7|) (< |i#0@@7| (|Seq#Length| |f#0@@21|))) (< (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@7|))) (|Seq#Length| |nodes#0@@1|)))))
 :qid |DLLDafny.95:14|
 :skolemid |1082|
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@7|)))
)) (=> (forall ((|i#1@@0| Int) ) (!  (=> true (=> (and (<= 0 |i#1@@0|) (< |i#1@@0| (|Seq#Length| |f#0@@21|))) (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#1@@0|)))))) |i#1@@0|)))
 :qid |DLLDafny.96:14|
 :skolemid |1081|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#1@@0|))))))
)) (=> (forall ((|p#0| Int) ) (!  (=> true (and (=> (and (<= 0 |p#0|) (< |p#0| (|Seq#Length| |g#0@@1|))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#0|))))) (=> (and (<= 0 |p#0|) (< |p#0| (|Seq#Length| |g#0@@1|))) (< (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#0|))) (|Seq#Length| |s#0@@11|)))))
 :qid |DLLDafny.97:14|
 :skolemid |1080|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#0|)))
)) (and (forall ((|p#1| Int) ) (!  (and (=> (<= 0 |p#1|) (=> (< |p#1| (|Seq#Length| |g#0@@1|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1|))))) (=> (=> (and (<= 0 |p#1|) (< |p#1| (|Seq#Length| |g#0@@1|))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1|))))) (=> (<= 0 |p#1|) (=> (< |p#1| (|Seq#Length| |g#0@@1|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1|)))))))
 :qid |DLLDafny.99:14|
 :skolemid |1070|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1|)))
)) (=> (forall ((|p#1@@0| Int) ) (!  (=> true (and (=> (and (<= 0 |p#1@@0|) (< |p#1@@0| (|Seq#Length| |g#0@@1|))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@0|))))) (=> (and (<= 0 |p#1@@0|) (< |p#1@@0| (|Seq#Length| |g#0@@1|))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@0|))) (|Seq#Length| |g#0@@1|)))))
 :qid |DLLDafny.99:14|
 :skolemid |1079|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@0|)))
)) (and (forall ((|p#2| Int) ) (!  (=> (<= 0 |p#2|) (=> (< |p#2| (|Seq#Length| |g#0@@1|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2|)))))
 :qid |DLLDafny.101:14|
 :skolemid |1071|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#2|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2|)))
)) (=> (forall ((|p#2@@0| Int) ) (!  (=> true (=> (and (<= 0 |p#2@@0|) (< |p#2@@0| (|Seq#Length| |g#0@@1|))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@0|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@0|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@0|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@0|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1078|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@0|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@0|)))
)) (=> (forall ((|p#3| Int) ) (!  (=> true (=> (and (and (<= 0 |p#3|) (< |p#3| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#3|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#3|))) (- 0 1)) (= |p#3| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1077|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#3|)))
)) (and (forall ((|p#4| Int) ) (!  (=> (<= 0 |p#4|) (=> (< |p#4| (|Seq#Length| |g#0@@1|)) (=> (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4|)))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4|)))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4|)))))) |p#4|) (and (|$IsA#_module.Option| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#4|)))) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#4|)))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1072|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#4|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4|))))))
 :pattern ( (|Seq#Index| |s#0@@11| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4|)))))
)) (=> (forall ((|p#4@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#4@@0|) (< |p#4@@0| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@0|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@0|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@0|)))))) |p#4@@0|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#4@@0|))) (|#_module.Option.Some| (|Seq#Index| |s#0@@11| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@0|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1076|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@0|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@0|))))))
 :pattern ( (|Seq#Index| |s#0@@11| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@0|)))))
)) (and (forall ((|p#5| Int) ) (!  (=> (<= 0 |p#5|) (=> (< |p#5| (|Seq#Length| |g#0@@1|)) (=> (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5|)))) (and (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5|))) (and (|_module.__default.Add#canCall| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5|))) 1) (=> (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5|))) 1) (|Seq#Length| |f#0@@21|)) (|_module.__default.Add#canCall| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5|))) 1)))))))
 :qid |DLLDafny.108:14|
 :skolemid |1073|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#5|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5|))))
)) (=> (forall ((|p#5@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#5@@0|) (< |p#5@@0| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@0|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5@@0|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@0|))) 1) (|Seq#Length| |f#0@@21|)) (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@0|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1075|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@0|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5@@0|))))
)) (forall ((|p#6| Int) ) (!  (=> (=> (and (and (<= 0 |p#6|) (< |p#6| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6|))))) true) (=> (<= 0 |p#6|) (=> (< |p#6| (|Seq#Length| |g#0@@1|)) (=> (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6|)))) (and (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#6|))) (and (=> (> (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6|))) 0) (|_module.__default.Sub#canCall| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6|))) 1)) (=> (>= 0 (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6|)))) (=> (not (or (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6|))) 0) (= (|Seq#Length| |f#0@@21|) 0))) (|_module.__default.Sub#canCall| (|Seq#Length| |f#0@@21|) 1)))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1074|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#6|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#6|))))
)))))))))))))))))))) (and (=> (_module.__default.Invs _module._default.Invs$A@@1 |nodes#0@@1| |freeStack#0@@1| |s#0@@11| |f#0@@21| |g#0@@1|) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (|Seq#Length| |f#0@@21|) (|Seq#Length| |s#0@@11|)) (= (|Seq#Length| |g#0@@1|) (|Seq#Length| |nodes#0@@1|))) (> (|Seq#Length| |nodes#0@@1|) 0)) (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| 0))) (- 0 1))) (and (<= 0 |freeStack#0@@1|) (< |freeStack#0@@1| (|Seq#Length| |nodes#0@@1|)))) (forall ((|i#0@@8| Int) ) (!  (=> true (and (=> (and (<= 0 |i#0@@8|) (< |i#0@@8| (|Seq#Length| |f#0@@21|))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@8|))))) (=> (and (<= 0 |i#0@@8|) (< |i#0@@8| (|Seq#Length| |f#0@@21|))) (< (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@8|))) (|Seq#Length| |nodes#0@@1|)))))
 :qid |DLLDafny.95:14|
 :skolemid |1061|
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@8|)))
))) (forall ((|i#1@@1| Int) ) (!  (=> true (=> (and (<= 0 |i#1@@1|) (< |i#1@@1| (|Seq#Length| |f#0@@21|))) (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#1@@1|)))))) |i#1@@1|)))
 :qid |DLLDafny.96:14|
 :skolemid |1062|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#1@@1|))))))
))) (forall ((|p#0@@0| Int) ) (!  (=> true (and (=> (and (<= 0 |p#0@@0|) (< |p#0@@0| (|Seq#Length| |g#0@@1|))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#0@@0|))))) (=> (and (<= 0 |p#0@@0|) (< |p#0@@0| (|Seq#Length| |g#0@@1|))) (< (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#0@@0|))) (|Seq#Length| |s#0@@11|)))))
 :qid |DLLDafny.97:14|
 :skolemid |1063|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#0@@0|)))
))) (forall ((|p#1@@1| Int) ) (!  (=> true (and (=> (and (<= 0 |p#1@@1|) (< |p#1@@1| (|Seq#Length| |g#0@@1|))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@1|))))) (=> (and (<= 0 |p#1@@1|) (< |p#1@@1| (|Seq#Length| |g#0@@1|))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@1|))) (|Seq#Length| |g#0@@1|)))))
 :qid |DLLDafny.99:14|
 :skolemid |1064|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@1|)))
))) (forall ((|p#2@@1| Int) ) (!  (=> true (=> (and (<= 0 |p#2@@1|) (< |p#2@@1| (|Seq#Length| |g#0@@1|))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@1|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@1|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@1|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@1|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1065|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@1|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@1|)))
))) (forall ((|p#3@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#3@@0|) (< |p#3@@0| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#3@@0|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#3@@0|))) (- 0 1)) (= |p#3@@0| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1066|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#3@@0|)))
))) (forall ((|p#4@@1| Int) ) (!  (=> true (=> (and (and (<= 0 |p#4@@1|) (< |p#4@@1| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@1|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@1|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@1|)))))) |p#4@@1|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#4@@1|))) (|#_module.Option.Some| (|Seq#Index| |s#0@@11| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@1|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1067|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@1|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@1|))))))
 :pattern ( (|Seq#Index| |s#0@@11| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@1|)))))
))) (forall ((|p#5@@1| Int) ) (!  (=> true (=> (and (and (<= 0 |p#5@@1|) (< |p#5@@1| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@1|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5@@1|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@1|))) 1) (|Seq#Length| |f#0@@21|)) (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@1|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1068|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@1|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5@@1|))))
))) (forall ((|p#6@@0| Int) ) (!  (=> true (and (=> (and (and (<= 0 |p#6@@0|) (< |p#6@@0| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@0|))))) true) (=> (and (and (<= 0 |p#6@@0|) (< |p#6@@0| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@0|))))) (= (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#6@@0|))) (ite (> (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@0|))) 0) (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@0|))) 1)))) (ite  (or (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@0|))) 0) (= (|Seq#Length| |f#0@@21|) 0)) 0 (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (_module.__default.Sub (|Seq#Length| |f#0@@21|) 1))))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1069|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@0|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#6@@0|))))
)))) (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= (|Seq#Length| |f#0@@21|) (|Seq#Length| |s#0@@11|)) (= (|Seq#Length| |g#0@@1|) (|Seq#Length| |nodes#0@@1|))) (> (|Seq#Length| |nodes#0@@1|) 0)) (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| 0))) (- 0 1))) (and (<= 0 |freeStack#0@@1|) (< |freeStack#0@@1| (|Seq#Length| |nodes#0@@1|)))) (forall ((|i#0@@9| Int) ) (!  (=> true (and (=> (and (<= 0 |i#0@@9|) (< |i#0@@9| (|Seq#Length| |f#0@@21|))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@9|))))) (=> (and (<= 0 |i#0@@9|) (< |i#0@@9| (|Seq#Length| |f#0@@21|))) (< (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@9|))) (|Seq#Length| |nodes#0@@1|)))))
 :qid |DLLDafny.95:14|
 :skolemid |1061|
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@21| |i#0@@9|)))
))) (forall ((|i#1@@2| Int) ) (!  (=> true (=> (and (<= 0 |i#1@@2|) (< |i#1@@2| (|Seq#Length| |f#0@@21|))) (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#1@@2|)))))) |i#1@@2|)))
 :qid |DLLDafny.96:14|
 :skolemid |1062|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| |i#1@@2|))))))
))) (forall ((|p#0@@1| Int) ) (!  (=> true (and (=> (and (<= 0 |p#0@@1|) (< |p#0@@1| (|Seq#Length| |g#0@@1|))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#0@@1|))))) (=> (and (<= 0 |p#0@@1|) (< |p#0@@1| (|Seq#Length| |g#0@@1|))) (< (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#0@@1|))) (|Seq#Length| |s#0@@11|)))))
 :qid |DLLDafny.97:14|
 :skolemid |1063|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#0@@1|)))
))) (forall ((|p#1@@2| Int) ) (!  (=> true (and (=> (and (<= 0 |p#1@@2|) (< |p#1@@2| (|Seq#Length| |g#0@@1|))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@2|))))) (=> (and (<= 0 |p#1@@2|) (< |p#1@@2| (|Seq#Length| |g#0@@1|))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@2|))) (|Seq#Length| |g#0@@1|)))))
 :qid |DLLDafny.99:14|
 :skolemid |1064|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#1@@2|)))
))) (forall ((|p#2@@2| Int) ) (!  (=> true (=> (and (<= 0 |p#2@@2|) (< |p#2@@2| (|Seq#Length| |g#0@@1|))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@2|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@2|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@2|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@2|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1065|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#2@@2|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#2@@2|)))
))) (forall ((|p#3@@1| Int) ) (!  (=> true (=> (and (and (<= 0 |p#3@@1|) (< |p#3@@1| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#3@@1|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#3@@1|))) (- 0 1)) (= |p#3@@1| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1066|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#3@@1|)))
))) (forall ((|p#4@@2| Int) ) (!  (=> true (=> (and (and (<= 0 |p#4@@2|) (< |p#4@@2| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@2|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@2|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@2|)))))) |p#4@@2|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#4@@2|))) (|#_module.Option.Some| (|Seq#Index| |s#0@@11| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@2|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1067|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@2|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@21| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@2|))))))
 :pattern ( (|Seq#Index| |s#0@@11| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#4@@2|)))))
))) (forall ((|p#5@@2| Int) ) (!  (=> true (=> (and (and (<= 0 |p#5@@2|) (< |p#5@@2| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@2|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5@@2|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@2|))) 1) (|Seq#Length| |f#0@@21|)) (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@2|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1068|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#5@@2|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#5@@2|))))
))) (forall ((|p#6@@1| Int) ) (!  (=> true (and (=> (and (and (<= 0 |p#6@@1|) (< |p#6@@1| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@1|))))) true) (=> (and (and (<= 0 |p#6@@1|) (< |p#6@@1| (|Seq#Length| |g#0@@1|))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@1|))))) (= (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#6@@1|))) (ite (> (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@1|))) 0) (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@1|))) 1)))) (ite  (or (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@1|))) 0) (= (|Seq#Length| |f#0@@21|) 0)) 0 (U_2_int ($Unbox intType (|Seq#Index| |f#0@@21| (_module.__default.Sub (|Seq#Length| |f#0@@21|) 1))))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1069|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@1| |p#6@@1|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@1| |p#6@@1|))))
))) (_module.__default.Invs _module._default.Invs$A@@1 |nodes#0@@1| |freeStack#0@@1| |s#0@@11| |f#0@@21| |g#0@@1|)))))
 :qid |unknown.0:0|
 :skolemid |1083|
 :pattern ( (_module.__default.Invs _module._default.Invs$A@@1 |nodes#0@@1| |freeStack#0@@1| |s#0@@11| |f#0@@21| |g#0@@1|))
))))
(assert  (=> (<= 11 $FunctionContextHeight) (forall ((_module._default.Invs$A@@2 T@U) (|nodes#0@@2| T@U) (|freeStack#0@@2| Int) (|s#0@@12| T@U) (|f#0@@22| T@U) (|g#0@@2| T@U) ) (!  (=> (and (and (and (and (and (= (type _module._default.Invs$A@@2) TyType) (= (type |nodes#0@@2|) (SeqType BoxType))) (= (type |s#0@@12|) (SeqType BoxType))) (= (type |f#0@@22|) (SeqType BoxType))) (= (type |g#0@@2|) (SeqType BoxType))) (or (|_module.__default.Invs#canCall| _module._default.Invs$A@@2 (Lit |nodes#0@@2|) |freeStack#0@@2| (Lit |s#0@@12|) (Lit |f#0@@22|) (Lit |g#0@@2|)) (and (not (= 11 $FunctionContextHeight)) (and (and (and ($Is |nodes#0@@2| (TSeq (Tclass._module.Node _module._default.Invs$A@@2))) ($Is |s#0@@12| (TSeq _module._default.Invs$A@@2))) ($Is |f#0@@22| (TSeq TInt))) ($Is |g#0@@2| (TSeq TInt)))))) (and (=> (= (|Seq#Length| (Lit |f#0@@22|)) (|Seq#Length| (Lit |s#0@@12|))) (=> (= (|Seq#Length| (Lit |g#0@@2|)) (|Seq#Length| (Lit |nodes#0@@2|))) (=> (> (|Seq#Length| (Lit |nodes#0@@2|)) 0) (=> (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) 0))) (- 0 1)) (=> (<= 0 |freeStack#0@@2|) (=> (< |freeStack#0@@2| (|Seq#Length| (Lit |nodes#0@@2|))) (=> (forall ((|i#2@@1| Int) ) (!  (=> true (and (=> (and (<= 0 |i#2@@1|) (< |i#2@@1| (|Seq#Length| (Lit |f#0@@22|)))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#2@@1|))))) (=> (and (<= 0 |i#2@@1|) (< |i#2@@1| (|Seq#Length| (Lit |f#0@@22|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#2@@1|))) (|Seq#Length| (Lit |nodes#0@@2|))))))
 :qid |DLLDafny.95:14|
 :skolemid |1105|
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@22| |i#2@@1|)))
)) (=> (forall ((|i#3| Int) ) (!  (=> true (=> (and (<= 0 |i#3|) (< |i#3| (|Seq#Length| (Lit |f#0@@22|)))) (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#3|)))))) |i#3|)))
 :qid |DLLDafny.96:14|
 :skolemid |1104|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@22| |i#3|))))))
)) (=> (forall ((|p#7| Int) ) (!  (=> true (and (=> (and (<= 0 |p#7|) (< |p#7| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#7|))))) (=> (and (<= 0 |p#7|) (< |p#7| (|Seq#Length| (Lit |g#0@@2|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#7|))) (|Seq#Length| (Lit |s#0@@12|))))))
 :qid |DLLDafny.97:14|
 :skolemid |1103|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#7|)))
)) (and (forall ((|p#8| Int) ) (!  (and (=> (<= 0 |p#8|) (=> (< |p#8| (|Seq#Length| (Lit |g#0@@2|))) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8|))))) (=> (=> (and (<= 0 |p#8|) (< |p#8| (|Seq#Length| (Lit |g#0@@2|)))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8|))))) (=> (<= 0 |p#8|) (=> (< |p#8| (|Seq#Length| (Lit |g#0@@2|))) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8|)))))))
 :qid |DLLDafny.99:14|
 :skolemid |1093|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#8|)))
)) (=> (forall ((|p#8@@0| Int) ) (!  (=> true (and (=> (and (<= 0 |p#8@@0|) (< |p#8@@0| (|Seq#Length| (Lit |g#0@@2|)))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8@@0|))))) (=> (and (<= 0 |p#8@@0|) (< |p#8@@0| (|Seq#Length| (Lit |g#0@@2|)))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8@@0|))) (|Seq#Length| (Lit |g#0@@2|))))))
 :qid |DLLDafny.99:14|
 :skolemid |1102|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#8@@0|)))
)) (and (forall ((|p#9| Int) ) (!  (=> (<= 0 |p#9|) (=> (< |p#9| (|Seq#Length| (Lit |g#0@@2|))) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#9|)))))
 :qid |DLLDafny.101:14|
 :skolemid |1094|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#9|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#9|)))
)) (=> (forall ((|p#9@@0| Int) ) (!  (=> true (=> (and (<= 0 |p#9@@0|) (< |p#9@@0| (|Seq#Length| (Lit |g#0@@2|)))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#9@@0|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#9@@0|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#9@@0|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#9@@0|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1101|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#9@@0|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#9@@0|)))
)) (=> (forall ((|p#10| Int) ) (!  (=> true (=> (and (and (<= 0 |p#10|) (< |p#10| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#10|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#10|))) (- 0 1)) (= |p#10| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1100|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#10|)))
)) (and (forall ((|p#11| Int) ) (!  (=> (<= 0 |p#11|) (=> (< |p#11| (|Seq#Length| (Lit |g#0@@2|))) (=> (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11|)))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11|)))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11|)))))) |p#11|) (and (|$IsA#_module.Option| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#11|)))) (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#11|)))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1095|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#11|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@22| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11|))))))
 :pattern ( (|Seq#Index| |s#0@@12| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11|)))))
)) (=> (forall ((|p#11@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#11@@0|) (< |p#11@@0| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@0|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@0|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@0|)))))) |p#11@@0|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#11@@0|))) (|#_module.Option.Some| (|Seq#Index| (Lit |s#0@@12|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@0|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1099|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@0|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@22| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@0|))))))
 :pattern ( (|Seq#Index| |s#0@@12| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@0|)))))
)) (and (forall ((|p#12| Int) ) (!  (=> (<= 0 |p#12|) (=> (< |p#12| (|Seq#Length| (Lit |g#0@@2|))) (=> (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12|)))) (and (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#12|))) (and (|_module.__default.Add#canCall| (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12|))) 1) (=> (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12|))) 1) (|Seq#Length| (Lit |f#0@@22|))) (|_module.__default.Add#canCall| (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12|))) 1)))))))
 :qid |DLLDafny.108:14|
 :skolemid |1096|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#12|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#12|))))
)) (=> (forall ((|p#12@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#12@@0|) (< |p#12@@0| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@0|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#12@@0|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@0|))) 1) (|Seq#Length| (Lit |f#0@@22|))) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@0|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1098|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#12@@0|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#12@@0|))))
)) (forall ((|p#13| Int) ) (!  (=> (=> (and (and (<= 0 |p#13|) (< |p#13| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13|))))) true) (=> (<= 0 |p#13|) (=> (< |p#13| (|Seq#Length| (Lit |g#0@@2|))) (=> (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13|)))) (and (_module.Node.Node_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#13|))) (and (=> (> (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13|))) 0) (|_module.__default.Sub#canCall| (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13|))) 1)) (=> (>= 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13|)))) (=> (not (or (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13|))) 0) (= (|Seq#Length| (Lit |f#0@@22|)) 0))) (|_module.__default.Sub#canCall| (|Seq#Length| (Lit |f#0@@22|)) 1)))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1097|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#13|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#13|))))
)))))))))))))))))))) (and (=> (_module.__default.Invs _module._default.Invs$A@@2 (Lit |nodes#0@@2|) |freeStack#0@@2| (Lit |s#0@@12|) (Lit |f#0@@22|) (Lit |g#0@@2|)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (|Seq#Length| (Lit |f#0@@22|)) (|Seq#Length| (Lit |s#0@@12|))) (= (|Seq#Length| (Lit |g#0@@2|)) (|Seq#Length| (Lit |nodes#0@@2|)))) (> (|Seq#Length| (Lit |nodes#0@@2|)) 0)) (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) 0))) (- 0 1))) (and (<= 0 |freeStack#0@@2|) (< |freeStack#0@@2| (|Seq#Length| (Lit |nodes#0@@2|))))) (forall ((|i#2@@2| Int) ) (!  (=> true (and (=> (and (<= 0 |i#2@@2|) (< |i#2@@2| (|Seq#Length| (Lit |f#0@@22|)))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#2@@2|))))) (=> (and (<= 0 |i#2@@2|) (< |i#2@@2| (|Seq#Length| (Lit |f#0@@22|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#2@@2|))) (|Seq#Length| (Lit |nodes#0@@2|))))))
 :qid |DLLDafny.95:14|
 :skolemid |1084|
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@22| |i#2@@2|)))
))) (forall ((|i#3@@0| Int) ) (!  (=> true (=> (and (<= 0 |i#3@@0|) (< |i#3@@0| (|Seq#Length| (Lit |f#0@@22|)))) (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#3@@0|)))))) |i#3@@0|)))
 :qid |DLLDafny.96:14|
 :skolemid |1085|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@22| |i#3@@0|))))))
))) (forall ((|p#7@@0| Int) ) (!  (=> true (and (=> (and (<= 0 |p#7@@0|) (< |p#7@@0| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#7@@0|))))) (=> (and (<= 0 |p#7@@0|) (< |p#7@@0| (|Seq#Length| (Lit |g#0@@2|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#7@@0|))) (|Seq#Length| (Lit |s#0@@12|))))))
 :qid |DLLDafny.97:14|
 :skolemid |1086|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#7@@0|)))
))) (forall ((|p#8@@1| Int) ) (!  (=> true (and (=> (and (<= 0 |p#8@@1|) (< |p#8@@1| (|Seq#Length| (Lit |g#0@@2|)))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8@@1|))))) (=> (and (<= 0 |p#8@@1|) (< |p#8@@1| (|Seq#Length| (Lit |g#0@@2|)))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8@@1|))) (|Seq#Length| (Lit |g#0@@2|))))))
 :qid |DLLDafny.99:14|
 :skolemid |1087|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#8@@1|)))
))) (forall ((|p#9@@1| Int) ) (!  (=> true (=> (and (<= 0 |p#9@@1|) (< |p#9@@1| (|Seq#Length| (Lit |g#0@@2|)))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#9@@1|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#9@@1|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#9@@1|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#9@@1|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1088|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#9@@1|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#9@@1|)))
))) (forall ((|p#10@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#10@@0|) (< |p#10@@0| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#10@@0|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#10@@0|))) (- 0 1)) (= |p#10@@0| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1089|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#10@@0|)))
))) (forall ((|p#11@@1| Int) ) (!  (=> true (=> (and (and (<= 0 |p#11@@1|) (< |p#11@@1| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@1|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@1|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@1|)))))) |p#11@@1|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#11@@1|))) (|#_module.Option.Some| (|Seq#Index| (Lit |s#0@@12|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@1|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1090|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@1|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@22| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@1|))))))
 :pattern ( (|Seq#Index| |s#0@@12| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@1|)))))
))) (forall ((|p#12@@1| Int) ) (!  (=> true (=> (and (and (<= 0 |p#12@@1|) (< |p#12@@1| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@1|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#12@@1|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@1|))) 1) (|Seq#Length| (Lit |f#0@@22|))) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@1|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1091|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#12@@1|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#12@@1|))))
))) (forall ((|p#13@@0| Int) ) (!  (=> true (and (=> (and (and (<= 0 |p#13@@0|) (< |p#13@@0| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@0|))))) true) (=> (and (and (<= 0 |p#13@@0|) (< |p#13@@0| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@0|))))) (= (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#13@@0|))) (ite (> (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@0|))) 0) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@0|))) 1)))) (ite  (or (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@0|))) 0) (= (|Seq#Length| (Lit |f#0@@22|)) 0)) 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (_module.__default.Sub (|Seq#Length| (Lit |f#0@@22|)) 1))))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1092|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#13@@0|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#13@@0|))))
)))) (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= (|Seq#Length| (Lit |f#0@@22|)) (|Seq#Length| (Lit |s#0@@12|))) (= (|Seq#Length| (Lit |g#0@@2|)) (|Seq#Length| (Lit |nodes#0@@2|)))) (> (|Seq#Length| (Lit |nodes#0@@2|)) 0)) (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) 0))) (- 0 1))) (and (<= 0 |freeStack#0@@2|) (< |freeStack#0@@2| (|Seq#Length| (Lit |nodes#0@@2|))))) (forall ((|i#2@@3| Int) ) (!  (=> true (and (=> (and (<= 0 |i#2@@3|) (< |i#2@@3| (|Seq#Length| (Lit |f#0@@22|)))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#2@@3|))))) (=> (and (<= 0 |i#2@@3|) (< |i#2@@3| (|Seq#Length| (Lit |f#0@@22|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#2@@3|))) (|Seq#Length| (Lit |nodes#0@@2|))))))
 :qid |DLLDafny.95:14|
 :skolemid |1084|
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@22| |i#2@@3|)))
))) (forall ((|i#3@@1| Int) ) (!  (=> true (=> (and (<= 0 |i#3@@1|) (< |i#3@@1| (|Seq#Length| (Lit |f#0@@22|)))) (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) |i#3@@1|)))))) |i#3@@1|)))
 :qid |DLLDafny.96:14|
 :skolemid |1085|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| (U_2_int ($Unbox intType (|Seq#Index| |f#0@@22| |i#3@@1|))))))
))) (forall ((|p#7@@1| Int) ) (!  (=> true (and (=> (and (<= 0 |p#7@@1|) (< |p#7@@1| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#7@@1|))))) (=> (and (<= 0 |p#7@@1|) (< |p#7@@1| (|Seq#Length| (Lit |g#0@@2|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#7@@1|))) (|Seq#Length| (Lit |s#0@@12|))))))
 :qid |DLLDafny.97:14|
 :skolemid |1086|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#7@@1|)))
))) (forall ((|p#8@@2| Int) ) (!  (=> true (and (=> (and (<= 0 |p#8@@2|) (< |p#8@@2| (|Seq#Length| (Lit |g#0@@2|)))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8@@2|))))) (=> (and (<= 0 |p#8@@2|) (< |p#8@@2| (|Seq#Length| (Lit |g#0@@2|)))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#8@@2|))) (|Seq#Length| (Lit |g#0@@2|))))))
 :qid |DLLDafny.99:14|
 :skolemid |1087|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#8@@2|)))
))) (forall ((|p#9@@2| Int) ) (!  (=> true (=> (and (<= 0 |p#9@@2|) (< |p#9@@2| (|Seq#Length| (Lit |g#0@@2|)))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#9@@2|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#9@@2|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#9@@2|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#9@@2|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1088|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#9@@2|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#9@@2|)))
))) (forall ((|p#10@@1| Int) ) (!  (=> true (=> (and (and (<= 0 |p#10@@1|) (< |p#10@@1| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#10@@1|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#10@@1|))) (- 0 1)) (= |p#10@@1| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1089|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#10@@1|)))
))) (forall ((|p#11@@2| Int) ) (!  (=> true (=> (and (and (<= 0 |p#11@@2|) (< |p#11@@2| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@2|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@2|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@2|)))))) |p#11@@2|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#11@@2|))) (|#_module.Option.Some| (|Seq#Index| (Lit |s#0@@12|) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#11@@2|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1090|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@2|)))
 :pattern ( ($Unbox intType (|Seq#Index| |f#0@@22| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@2|))))))
 :pattern ( (|Seq#Index| |s#0@@12| (U_2_int ($Unbox intType (|Seq#Index| |g#0@@2| |p#11@@2|)))))
))) (forall ((|p#12@@2| Int) ) (!  (=> true (=> (and (and (<= 0 |p#12@@2|) (< |p#12@@2| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@2|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#12@@2|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@2|))) 1) (|Seq#Length| (Lit |f#0@@22|))) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#12@@2|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1091|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#12@@2|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#12@@2|))))
))) (forall ((|p#13@@1| Int) ) (!  (=> true (and (=> (and (and (<= 0 |p#13@@1|) (< |p#13@@1| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@1|))))) true) (=> (and (and (<= 0 |p#13@@1|) (< |p#13@@1| (|Seq#Length| (Lit |g#0@@2|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@1|))))) (= (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| (Lit |nodes#0@@2|) |p#13@@1|))) (ite (> (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@1|))) 0) (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@1|))) 1)))) (ite  (or (= (U_2_int ($Unbox intType (|Seq#Index| (Lit |g#0@@2|) |p#13@@1|))) 0) (= (|Seq#Length| (Lit |f#0@@22|)) 0)) 0 (U_2_int ($Unbox intType (|Seq#Index| (Lit |f#0@@22|) (_module.__default.Sub (|Seq#Length| (Lit |f#0@@22|)) 1))))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1092|
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@@2| |p#13@@1|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| |nodes#0@@2| |p#13@@1|))))
))) (_module.__default.Invs _module._default.Invs$A@@2 (Lit |nodes#0@@2|) |freeStack#0@@2| (Lit |s#0@@12|) (Lit |f#0@@22|) (Lit |g#0@@2|))))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1106|
 :pattern ( (_module.__default.Invs _module._default.Invs$A@@2 (Lit |nodes#0@@2|) |freeStack#0@@2| (Lit |s#0@@12|) (Lit |f#0@@22|) (Lit |g#0@@2|)))
))))
(assert  (=> (<= 12 $FunctionContextHeight) (forall ((_module._default.Inv$A T@U) (|l#0| T@U) ) (!  (=> (and (and (= (type _module._default.Inv$A) TyType) (= (type |l#0|) DatatypeTypeType)) (or (|_module.__default.Inv#canCall| _module._default.Inv$A |l#0|) (and (not (= 12 $FunctionContextHeight)) ($Is |l#0| (Tclass._module.DList _module._default.Inv$A))))) true)
 :qid |unknown.0:0|
 :skolemid |1169|
 :pattern ( (_module.__default.Inv _module._default.Inv$A |l#0|))
))))
(assert (forall ((_module._default.Inv$A@@0 T@U) (|l#0@@0| T@U) ) (!  (=> (and (and (= (type _module._default.Inv$A@@0) TyType) (= (type |l#0@@0|) DatatypeTypeType)) ($Is |l#0@@0| (Tclass._module.DList _module._default.Inv$A@@0))) (and (=> (|_module.__default.Inv#requires| _module._default.Inv$A@@0 |l#0@@0|) true) (=> true (|_module.__default.Inv#requires| _module._default.Inv$A@@0 |l#0@@0|))))
 :qid |unknown.0:0|
 :skolemid |1170|
 :pattern ( (|_module.__default.Inv#requires| _module._default.Inv$A@@0 |l#0@@0|))
)))
(assert  (=> (<= 12 $FunctionContextHeight) (forall ((_module._default.Inv$A@@1 T@U) (|l#0@@1| T@U) ) (!  (=> (and (and (= (type _module._default.Inv$A@@1) TyType) (= (type |l#0@@1|) DatatypeTypeType)) (or (|_module.__default.Inv#canCall| _module._default.Inv$A@@1 |l#0@@1|) (and (not (= 12 $FunctionContextHeight)) ($Is |l#0@@1| (Tclass._module.DList _module._default.Inv$A@@1))))) (and (and (and (and (and (and (_module.DList.DList_q |l#0@@1|) (_module.DList.DList_q |l#0@@1|)) (_module.DList.DList_q |l#0@@1|)) (_module.DList.DList_q |l#0@@1|)) (_module.DList.DList_q |l#0@@1|)) (|_module.__default.Invs#canCall| _module._default.Inv$A@@1 (_module.DList.nodes |l#0@@1|) (_module.DList.freeStack |l#0@@1|) (_module.DList.s |l#0@@1|) (_module.DList.f |l#0@@1|) (_module.DList.g |l#0@@1|))) (and (=> (_module.__default.Inv _module._default.Inv$A@@1 |l#0@@1|) (_module.__default.Invs _module._default.Inv$A@@1 (_module.DList.nodes |l#0@@1|) (_module.DList.freeStack |l#0@@1|) (_module.DList.s |l#0@@1|) (_module.DList.f |l#0@@1|) (_module.DList.g |l#0@@1|))) (=> (_module.__default.Invs _module._default.Inv$A@@1 (_module.DList.nodes |l#0@@1|) (_module.DList.freeStack |l#0@@1|) (_module.DList.s |l#0@@1|) (_module.DList.f |l#0@@1|) (_module.DList.g |l#0@@1|)) (_module.__default.Inv _module._default.Inv$A@@1 |l#0@@1|)))))
 :qid |unknown.0:0|
 :skolemid |1171|
 :pattern ( (_module.__default.Inv _module._default.Inv$A@@1 |l#0@@1|))
))))
(assert  (=> (<= 12 $FunctionContextHeight) (forall ((_module._default.Inv$A@@2 T@U) (|l#0@@2| T@U) ) (!  (=> (and (and (= (type _module._default.Inv$A@@2) TyType) (= (type |l#0@@2|) DatatypeTypeType)) (or (|_module.__default.Inv#canCall| _module._default.Inv$A@@2 (Lit |l#0@@2|)) (and (not (= 12 $FunctionContextHeight)) ($Is |l#0@@2| (Tclass._module.DList _module._default.Inv$A@@2))))) (and (and (and (and (and (and (_module.DList.DList_q (Lit |l#0@@2|)) (_module.DList.DList_q (Lit |l#0@@2|))) (_module.DList.DList_q (Lit |l#0@@2|))) (_module.DList.DList_q (Lit |l#0@@2|))) (_module.DList.DList_q (Lit |l#0@@2|))) (|_module.__default.Invs#canCall| _module._default.Inv$A@@2 (Lit (_module.DList.nodes (Lit |l#0@@2|))) (_module.DList.freeStack (Lit |l#0@@2|)) (Lit (_module.DList.s (Lit |l#0@@2|))) (Lit (_module.DList.f (Lit |l#0@@2|))) (Lit (_module.DList.g (Lit |l#0@@2|))))) (and (=> (_module.__default.Inv _module._default.Inv$A@@2 (Lit |l#0@@2|)) (U_2_bool (Lit (bool_2_U (_module.__default.Invs _module._default.Inv$A@@2 (Lit (_module.DList.nodes (Lit |l#0@@2|))) (_module.DList.freeStack (Lit |l#0@@2|)) (Lit (_module.DList.s (Lit |l#0@@2|))) (Lit (_module.DList.f (Lit |l#0@@2|))) (Lit (_module.DList.g (Lit |l#0@@2|)))))))) (=> (U_2_bool (Lit (bool_2_U (_module.__default.Invs _module._default.Inv$A@@2 (Lit (_module.DList.nodes (Lit |l#0@@2|))) (_module.DList.freeStack (Lit |l#0@@2|)) (Lit (_module.DList.s (Lit |l#0@@2|))) (Lit (_module.DList.f (Lit |l#0@@2|))) (Lit (_module.DList.g (Lit |l#0@@2|))))))) (_module.__default.Inv _module._default.Inv$A@@2 (Lit |l#0@@2|))))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1172|
 :pattern ( (_module.__default.Inv _module._default.Inv$A@@2 (Lit |l#0@@2|)))
))))
(assert (forall ((arg0@@249 T@U) (arg1@@116 T@U) ) (! (= (type (_module.__default.Seq arg0@@249 arg1@@116)) (SeqType BoxType))
 :qid |funType:_module.__default.Seq|
 :pattern ( (_module.__default.Seq arg0@@249 arg1@@116))
)))
(assert  (=> (<= 13 $FunctionContextHeight) (forall ((_module._default.Seq$A T@U) (|l#0@@3| T@U) ) (!  (=> (and (and (= (type _module._default.Seq$A) TyType) (= (type |l#0@@3|) DatatypeTypeType)) (or (|_module.__default.Seq#canCall| _module._default.Seq$A |l#0@@3|) (and (not (= 13 $FunctionContextHeight)) ($Is |l#0@@3| (Tclass._module.DList _module._default.Seq$A))))) ($Is (_module.__default.Seq _module._default.Seq$A |l#0@@3|) (TSeq _module._default.Seq$A)))
 :qid |unknown.0:0|
 :skolemid |1174|
 :pattern ( (_module.__default.Seq _module._default.Seq$A |l#0@@3|))
))))
(assert (forall ((_module._default.Seq$A@@0 T@U) (|l#0@@4| T@U) ) (!  (=> (and (and (= (type _module._default.Seq$A@@0) TyType) (= (type |l#0@@4|) DatatypeTypeType)) ($Is |l#0@@4| (Tclass._module.DList _module._default.Seq$A@@0))) (and (=> (|_module.__default.Seq#requires| _module._default.Seq$A@@0 |l#0@@4|) true) (=> true (|_module.__default.Seq#requires| _module._default.Seq$A@@0 |l#0@@4|))))
 :qid |unknown.0:0|
 :skolemid |1175|
 :pattern ( (|_module.__default.Seq#requires| _module._default.Seq$A@@0 |l#0@@4|))
)))
(assert  (=> (<= 13 $FunctionContextHeight) (forall ((_module._default.Seq$A@@1 T@U) (|l#0@@5| T@U) ) (!  (=> (and (and (= (type _module._default.Seq$A@@1) TyType) (= (type |l#0@@5|) DatatypeTypeType)) (or (|_module.__default.Seq#canCall| _module._default.Seq$A@@1 |l#0@@5|) (and (not (= 13 $FunctionContextHeight)) ($Is |l#0@@5| (Tclass._module.DList _module._default.Seq$A@@1))))) (and (_module.DList.DList_q |l#0@@5|) (= (_module.__default.Seq _module._default.Seq$A@@1 |l#0@@5|) (_module.DList.s |l#0@@5|))))
 :qid |unknown.0:0|
 :skolemid |1176|
 :pattern ( (_module.__default.Seq _module._default.Seq$A@@1 |l#0@@5|))
))))
(assert  (=> (<= 13 $FunctionContextHeight) (forall ((_module._default.Seq$A@@2 T@U) (|l#0@@6| T@U) ) (!  (=> (and (and (= (type _module._default.Seq$A@@2) TyType) (= (type |l#0@@6|) DatatypeTypeType)) (or (|_module.__default.Seq#canCall| _module._default.Seq$A@@2 (Lit |l#0@@6|)) (and (not (= 13 $FunctionContextHeight)) ($Is |l#0@@6| (Tclass._module.DList _module._default.Seq$A@@2))))) (and (_module.DList.DList_q (Lit |l#0@@6|)) (= (_module.__default.Seq _module._default.Seq$A@@2 (Lit |l#0@@6|)) (Lit (_module.DList.s (Lit |l#0@@6|))))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1177|
 :pattern ( (_module.__default.Seq _module._default.Seq$A@@2 (Lit |l#0@@6|)))
))))
(assert  (=> (<= 14 $FunctionContextHeight) (forall ((_module._default.ValidPtr$A T@U) (|l#0@@7| T@U) (|p#0@@2| Int) ) (!  (=> (and (and (and (= (type _module._default.ValidPtr$A) TyType) (= (type |l#0@@7|) DatatypeTypeType)) (or (|_module.__default.ValidPtr#canCall| _module._default.ValidPtr$A |l#0@@7| |p#0@@2|) (and (not (= 14 $FunctionContextHeight)) ($Is |l#0@@7| (Tclass._module.DList _module._default.ValidPtr$A))))) (_module.__default.ValidPtr _module._default.ValidPtr$A |l#0@@7| |p#0@@2|)) (not (= |p#0@@2| 0)))
 :qid |unknown.0:0|
 :skolemid |1178|
 :pattern ( (_module.__default.ValidPtr _module._default.ValidPtr$A |l#0@@7| |p#0@@2|))
))))
(assert (forall ((_module._default.ValidPtr$A@@0 T@U) (|l#0@@8| T@U) (|p#0@@3| Int) ) (!  (=> (and (and (= (type _module._default.ValidPtr$A@@0) TyType) (= (type |l#0@@8|) DatatypeTypeType)) ($Is |l#0@@8| (Tclass._module.DList _module._default.ValidPtr$A@@0))) (and (=> (|_module.__default.ValidPtr#requires| _module._default.ValidPtr$A@@0 |l#0@@8| |p#0@@3|) true) (=> true (|_module.__default.ValidPtr#requires| _module._default.ValidPtr$A@@0 |l#0@@8| |p#0@@3|))))
 :qid |unknown.0:0|
 :skolemid |1179|
 :pattern ( (|_module.__default.ValidPtr#requires| _module._default.ValidPtr$A@@0 |l#0@@8| |p#0@@3|))
)))
(assert  (=> (<= 14 $FunctionContextHeight) (forall ((_module._default.ValidPtr$A@@1 T@U) (|l#0@@9| T@U) (|p#0@@4| Int) ) (!  (=> (and (and (= (type _module._default.ValidPtr$A@@1) TyType) (= (type |l#0@@9|) DatatypeTypeType)) (or (|_module.__default.ValidPtr#canCall| _module._default.ValidPtr$A@@1 |l#0@@9| |p#0@@4|) (and (not (= 14 $FunctionContextHeight)) ($Is |l#0@@9| (Tclass._module.DList _module._default.ValidPtr$A@@1))))) (and (=> (< 0 |p#0@@4|) (and (_module.DList.DList_q |l#0@@9|) (=> (< |p#0@@4| (|Seq#Length| (_module.DList.g |l#0@@9|))) (_module.DList.DList_q |l#0@@9|)))) (and (=> (_module.__default.ValidPtr _module._default.ValidPtr$A@@1 |l#0@@9| |p#0@@4|) (and (and (< 0 |p#0@@4|) (< |p#0@@4| (|Seq#Length| (_module.DList.g |l#0@@9|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l#0@@9|) |p#0@@4|))) 0))) (=> (and (and (< 0 |p#0@@4|) (< |p#0@@4| (|Seq#Length| (_module.DList.g |l#0@@9|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l#0@@9|) |p#0@@4|))) 0)) (_module.__default.ValidPtr _module._default.ValidPtr$A@@1 |l#0@@9| |p#0@@4|)))))
 :qid |unknown.0:0|
 :skolemid |1180|
 :pattern ( (_module.__default.ValidPtr _module._default.ValidPtr$A@@1 |l#0@@9| |p#0@@4|))
))))
(assert  (=> (<= 14 $FunctionContextHeight) (forall ((_module._default.ValidPtr$A@@2 T@U) (|l#0@@10| T@U) (|p#0@@5| Int) ) (!  (=> (and (and (= (type _module._default.ValidPtr$A@@2) TyType) (= (type |l#0@@10|) DatatypeTypeType)) (or (|_module.__default.ValidPtr#canCall| _module._default.ValidPtr$A@@2 (Lit |l#0@@10|) |p#0@@5|) (and (not (= 14 $FunctionContextHeight)) ($Is |l#0@@10| (Tclass._module.DList _module._default.ValidPtr$A@@2))))) (and (=> (U_2_bool (Lit (bool_2_U (< 0 |p#0@@5|)))) (and (_module.DList.DList_q (Lit |l#0@@10|)) (=> (< |p#0@@5| (|Seq#Length| (Lit (_module.DList.g (Lit |l#0@@10|))))) (_module.DList.DList_q (Lit |l#0@@10|))))) (and (=> (_module.__default.ValidPtr _module._default.ValidPtr$A@@2 (Lit |l#0@@10|) |p#0@@5|) (and (and (< 0 |p#0@@5|) (< |p#0@@5| (|Seq#Length| (Lit (_module.DList.g (Lit |l#0@@10|)))))) (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit (_module.DList.g (Lit |l#0@@10|))) |p#0@@5|))) 0))) (=> (and (and (< 0 |p#0@@5|) (< |p#0@@5| (|Seq#Length| (Lit (_module.DList.g (Lit |l#0@@10|)))))) (>= (U_2_int ($Unbox intType (|Seq#Index| (Lit (_module.DList.g (Lit |l#0@@10|))) |p#0@@5|))) 0)) (_module.__default.ValidPtr _module._default.ValidPtr$A@@2 (Lit |l#0@@10|) |p#0@@5|)))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1181|
 :pattern ( (_module.__default.ValidPtr _module._default.ValidPtr$A@@2 (Lit |l#0@@10|) |p#0@@5|))
))))
(assert  (=> (<= 15 $FunctionContextHeight) (forall ((_module._default.MaybePtr$A T@U) (|l#0@@11| T@U) (|p#0@@6| Int) ) (!  (=> (and (and (= (type _module._default.MaybePtr$A) TyType) (= (type |l#0@@11|) DatatypeTypeType)) (or (|_module.__default.MaybePtr#canCall| _module._default.MaybePtr$A |l#0@@11| |p#0@@6|) (and (not (= 15 $FunctionContextHeight)) ($Is |l#0@@11| (Tclass._module.DList _module._default.MaybePtr$A))))) true)
 :qid |unknown.0:0|
 :skolemid |1182|
 :pattern ( (_module.__default.MaybePtr _module._default.MaybePtr$A |l#0@@11| |p#0@@6|))
))))
(assert (forall ((_module._default.MaybePtr$A@@0 T@U) (|l#0@@12| T@U) (|p#0@@7| Int) ) (!  (=> (and (and (= (type _module._default.MaybePtr$A@@0) TyType) (= (type |l#0@@12|) DatatypeTypeType)) ($Is |l#0@@12| (Tclass._module.DList _module._default.MaybePtr$A@@0))) (and (=> (|_module.__default.MaybePtr#requires| _module._default.MaybePtr$A@@0 |l#0@@12| |p#0@@7|) true) (=> true (|_module.__default.MaybePtr#requires| _module._default.MaybePtr$A@@0 |l#0@@12| |p#0@@7|))))
 :qid |unknown.0:0|
 :skolemid |1183|
 :pattern ( (|_module.__default.MaybePtr#requires| _module._default.MaybePtr$A@@0 |l#0@@12| |p#0@@7|))
)))
(assert  (=> (<= 15 $FunctionContextHeight) (forall ((_module._default.MaybePtr$A@@1 T@U) (|l#0@@13| T@U) (|p#0@@8| Int) ) (!  (=> (and (and (= (type _module._default.MaybePtr$A@@1) TyType) (= (type |l#0@@13|) DatatypeTypeType)) (or (|_module.__default.MaybePtr#canCall| _module._default.MaybePtr$A@@1 |l#0@@13| |p#0@@8|) (and (not (= 15 $FunctionContextHeight)) ($Is |l#0@@13| (Tclass._module.DList _module._default.MaybePtr$A@@1))))) (and (=> (not (= |p#0@@8| 0)) (|_module.__default.ValidPtr#canCall| _module._default.MaybePtr$A@@1 |l#0@@13| |p#0@@8|)) (and (=> (_module.__default.MaybePtr _module._default.MaybePtr$A@@1 |l#0@@13| |p#0@@8|) (or (= |p#0@@8| 0) (_module.__default.ValidPtr _module._default.MaybePtr$A@@1 |l#0@@13| |p#0@@8|))) (=> (or (= |p#0@@8| 0) (_module.__default.ValidPtr _module._default.MaybePtr$A@@1 |l#0@@13| |p#0@@8|)) (_module.__default.MaybePtr _module._default.MaybePtr$A@@1 |l#0@@13| |p#0@@8|)))))
 :qid |unknown.0:0|
 :skolemid |1184|
 :pattern ( (_module.__default.MaybePtr _module._default.MaybePtr$A@@1 |l#0@@13| |p#0@@8|))
))))
(assert  (=> (<= 15 $FunctionContextHeight) (forall ((_module._default.MaybePtr$A@@2 T@U) (|l#0@@14| T@U) (|p#0@@9| Int) ) (!  (=> (and (and (= (type _module._default.MaybePtr$A@@2) TyType) (= (type |l#0@@14|) DatatypeTypeType)) (or (|_module.__default.MaybePtr#canCall| _module._default.MaybePtr$A@@2 (Lit |l#0@@14|) |p#0@@9|) (and (not (= 15 $FunctionContextHeight)) ($Is |l#0@@14| (Tclass._module.DList _module._default.MaybePtr$A@@2))))) (and (=> (not (= |p#0@@9| 0)) (|_module.__default.ValidPtr#canCall| _module._default.MaybePtr$A@@2 (Lit |l#0@@14|) |p#0@@9|)) (and (=> (_module.__default.MaybePtr _module._default.MaybePtr$A@@2 (Lit |l#0@@14|) |p#0@@9|) (or (= |p#0@@9| 0) (_module.__default.ValidPtr _module._default.MaybePtr$A@@2 (Lit |l#0@@14|) |p#0@@9|))) (=> (or (= |p#0@@9| 0) (_module.__default.ValidPtr _module._default.MaybePtr$A@@2 (Lit |l#0@@14|) |p#0@@9|)) (_module.__default.MaybePtr _module._default.MaybePtr$A@@2 (Lit |l#0@@14|) |p#0@@9|)))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1185|
 :pattern ( (_module.__default.MaybePtr _module._default.MaybePtr$A@@2 (Lit |l#0@@14|) |p#0@@9|))
))))
(assert  (=> (<= 16 $FunctionContextHeight) (forall ((_module._default.Index$A T@U) (|l#0@@15| T@U) (|p#0@@10| Int) ) (!  (=> (and (and (= (type _module._default.Index$A) TyType) (= (type |l#0@@15|) DatatypeTypeType)) (or (|_module.__default.Index#canCall| _module._default.Index$A |l#0@@15| |p#0@@10|) (and (not (= 16 $FunctionContextHeight)) ($Is |l#0@@15| (Tclass._module.DList _module._default.Index$A))))) (and (=> (and (_module.__default.Inv _module._default.Index$A |l#0@@15|) (_module.__default.ValidPtr _module._default.Index$A |l#0@@15| |p#0@@10|)) (and (<= 0 (_module.__default.Index _module._default.Index$A |l#0@@15| |p#0@@10|)) (< (_module.__default.Index _module._default.Index$A |l#0@@15| |p#0@@10|) (|Seq#Length| (_module.__default.Seq _module._default.Index$A |l#0@@15|))))) (=> (and (_module.__default.Inv _module._default.Index$A |l#0@@15|) (= |p#0@@10| 0)) (= (_module.__default.Index _module._default.Index$A |l#0@@15| |p#0@@10|) (- 0 1)))))
 :qid |unknown.0:0|
 :skolemid |1187|
 :pattern ( (_module.__default.Index _module._default.Index$A |l#0@@15| |p#0@@10|))
))))
(assert (forall ((_module._default.Index$A@@0 T@U) (|l#0@@16| T@U) (|p#0@@11| Int) ) (!  (=> (and (and (= (type _module._default.Index$A@@0) TyType) (= (type |l#0@@16|) DatatypeTypeType)) ($Is |l#0@@16| (Tclass._module.DList _module._default.Index$A@@0))) (and (=> (|_module.__default.Index#requires| _module._default.Index$A@@0 |l#0@@16| |p#0@@11|) true) (=> true (|_module.__default.Index#requires| _module._default.Index$A@@0 |l#0@@16| |p#0@@11|))))
 :qid |unknown.0:0|
 :skolemid |1188|
 :pattern ( (|_module.__default.Index#requires| _module._default.Index$A@@0 |l#0@@16| |p#0@@11|))
)))
(assert  (=> (<= 16 $FunctionContextHeight) (forall ((_module._default.Index$A@@1 T@U) (|l#0@@17| T@U) (|p#0@@12| Int) ) (!  (=> (and (and (= (type _module._default.Index$A@@1) TyType) (= (type |l#0@@17|) DatatypeTypeType)) (or (|_module.__default.Index#canCall| _module._default.Index$A@@1 |l#0@@17| |p#0@@12|) (and (not (= 16 $FunctionContextHeight)) ($Is |l#0@@17| (Tclass._module.DList _module._default.Index$A@@1))))) (and (and (and (|_module.__default.Inv#canCall| _module._default.Index$A@@1 |l#0@@17|) (=> (_module.__default.Inv _module._default.Index$A@@1 |l#0@@17|) (|_module.__default.MaybePtr#canCall| _module._default.Index$A@@1 |l#0@@17| |p#0@@12|))) (=> (and (_module.__default.Inv _module._default.Index$A@@1 |l#0@@17|) (_module.__default.MaybePtr _module._default.Index$A@@1 |l#0@@17| |p#0@@12|)) (_module.DList.DList_q |l#0@@17|))) (= (_module.__default.Index _module._default.Index$A@@1 |l#0@@17| |p#0@@12|) (ite  (and (_module.__default.Inv _module._default.Index$A@@1 |l#0@@17|) (_module.__default.MaybePtr _module._default.Index$A@@1 |l#0@@17| |p#0@@12|)) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l#0@@17|) |p#0@@12|))) 0))))
 :qid |unknown.0:0|
 :skolemid |1189|
 :pattern ( (_module.__default.Index _module._default.Index$A@@1 |l#0@@17| |p#0@@12|))
))))
(assert  (=> (<= 16 $FunctionContextHeight) (forall ((_module._default.Index$A@@2 T@U) (|l#0@@18| T@U) (|p#0@@13| Int) ) (!  (=> (and (and (= (type _module._default.Index$A@@2) TyType) (= (type |l#0@@18|) DatatypeTypeType)) (or (|_module.__default.Index#canCall| _module._default.Index$A@@2 (Lit |l#0@@18|) |p#0@@13|) (and (not (= 16 $FunctionContextHeight)) ($Is |l#0@@18| (Tclass._module.DList _module._default.Index$A@@2))))) (and (and (and (|_module.__default.Inv#canCall| _module._default.Index$A@@2 (Lit |l#0@@18|)) (=> (U_2_bool (Lit (bool_2_U (_module.__default.Inv _module._default.Index$A@@2 (Lit |l#0@@18|))))) (|_module.__default.MaybePtr#canCall| _module._default.Index$A@@2 (Lit |l#0@@18|) |p#0@@13|))) (=> (U_2_bool (Lit (bool_2_U  (and (_module.__default.Inv _module._default.Index$A@@2 (Lit |l#0@@18|)) (_module.__default.MaybePtr _module._default.Index$A@@2 (Lit |l#0@@18|) |p#0@@13|))))) (_module.DList.DList_q (Lit |l#0@@18|)))) (= (_module.__default.Index _module._default.Index$A@@2 (Lit |l#0@@18|) |p#0@@13|) (ite  (and (_module.__default.Inv _module._default.Index$A@@2 (Lit |l#0@@18|)) (_module.__default.MaybePtr _module._default.Index$A@@2 (Lit |l#0@@18|) |p#0@@13|)) (U_2_int ($Unbox intType (|Seq#Index| (Lit (_module.DList.g (Lit |l#0@@18|))) |p#0@@13|))) 0))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1190|
 :pattern ( (_module.__default.Index _module._default.Index$A@@2 (Lit |l#0@@18|) |p#0@@13|))
))))
(assert  (=> (<= 17 $FunctionContextHeight) (forall ((_module._default.IndexHi$A T@U) (|l#0@@19| T@U) (|p#0@@14| Int) ) (!  (=> (and (and (= (type _module._default.IndexHi$A) TyType) (= (type |l#0@@19|) DatatypeTypeType)) (or (|_module.__default.IndexHi#canCall| _module._default.IndexHi$A |l#0@@19| |p#0@@14|) (and (not (= 17 $FunctionContextHeight)) ($Is |l#0@@19| (Tclass._module.DList _module._default.IndexHi$A))))) (and (=> (and (_module.__default.Inv _module._default.IndexHi$A |l#0@@19|) (_module.__default.ValidPtr _module._default.IndexHi$A |l#0@@19| |p#0@@14|)) (= (_module.__default.IndexHi _module._default.IndexHi$A |l#0@@19| |p#0@@14|) (_module.__default.Index _module._default.IndexHi$A |l#0@@19| |p#0@@14|))) (=> (and (_module.__default.Inv _module._default.IndexHi$A |l#0@@19|) (= |p#0@@14| 0)) (= (_module.__default.IndexHi _module._default.IndexHi$A |l#0@@19| |p#0@@14|) (|Seq#Length| (_module.__default.Seq _module._default.IndexHi$A |l#0@@19|))))))
 :qid |unknown.0:0|
 :skolemid |1193|
 :pattern ( (_module.__default.IndexHi _module._default.IndexHi$A |l#0@@19| |p#0@@14|))
))))
(assert (forall ((_module._default.IndexHi$A@@0 T@U) (|l#0@@20| T@U) (|p#0@@15| Int) ) (!  (=> (and (and (= (type _module._default.IndexHi$A@@0) TyType) (= (type |l#0@@20|) DatatypeTypeType)) ($Is |l#0@@20| (Tclass._module.DList _module._default.IndexHi$A@@0))) (and (=> (|_module.__default.IndexHi#requires| _module._default.IndexHi$A@@0 |l#0@@20| |p#0@@15|) true) (=> true (|_module.__default.IndexHi#requires| _module._default.IndexHi$A@@0 |l#0@@20| |p#0@@15|))))
 :qid |unknown.0:0|
 :skolemid |1194|
 :pattern ( (|_module.__default.IndexHi#requires| _module._default.IndexHi$A@@0 |l#0@@20| |p#0@@15|))
)))
(assert  (=> (<= 17 $FunctionContextHeight) (forall ((_module._default.IndexHi$A@@1 T@U) (|l#0@@21| T@U) (|p#0@@16| Int) ) (!  (=> (and (and (= (type _module._default.IndexHi$A@@1) TyType) (= (type |l#0@@21|) DatatypeTypeType)) (or (|_module.__default.IndexHi#canCall| _module._default.IndexHi$A@@1 |l#0@@21| |p#0@@16|) (and (not (= 17 $FunctionContextHeight)) ($Is |l#0@@21| (Tclass._module.DList _module._default.IndexHi$A@@1))))) (and (and (and (and (|_module.__default.Inv#canCall| _module._default.IndexHi$A@@1 |l#0@@21|) (=> (_module.__default.Inv _module._default.IndexHi$A@@1 |l#0@@21|) (|_module.__default.ValidPtr#canCall| _module._default.IndexHi$A@@1 |l#0@@21| |p#0@@16|))) (=> (and (_module.__default.Inv _module._default.IndexHi$A@@1 |l#0@@21|) (_module.__default.ValidPtr _module._default.IndexHi$A@@1 |l#0@@21| |p#0@@16|)) (_module.DList.DList_q |l#0@@21|))) (=> (not (and (_module.__default.Inv _module._default.IndexHi$A@@1 |l#0@@21|) (_module.__default.ValidPtr _module._default.IndexHi$A@@1 |l#0@@21| |p#0@@16|))) (_module.DList.DList_q |l#0@@21|))) (= (_module.__default.IndexHi _module._default.IndexHi$A@@1 |l#0@@21| |p#0@@16|) (ite  (and (_module.__default.Inv _module._default.IndexHi$A@@1 |l#0@@21|) (_module.__default.ValidPtr _module._default.IndexHi$A@@1 |l#0@@21| |p#0@@16|)) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l#0@@21|) |p#0@@16|))) (|Seq#Length| (_module.DList.s |l#0@@21|))))))
 :qid |unknown.0:0|
 :skolemid |1195|
 :pattern ( (_module.__default.IndexHi _module._default.IndexHi$A@@1 |l#0@@21| |p#0@@16|))
))))
(assert  (=> (<= 17 $FunctionContextHeight) (forall ((_module._default.IndexHi$A@@2 T@U) (|l#0@@22| T@U) (|p#0@@17| Int) ) (!  (=> (and (and (= (type _module._default.IndexHi$A@@2) TyType) (= (type |l#0@@22|) DatatypeTypeType)) (or (|_module.__default.IndexHi#canCall| _module._default.IndexHi$A@@2 (Lit |l#0@@22|) |p#0@@17|) (and (not (= 17 $FunctionContextHeight)) ($Is |l#0@@22| (Tclass._module.DList _module._default.IndexHi$A@@2))))) (and (and (and (and (|_module.__default.Inv#canCall| _module._default.IndexHi$A@@2 (Lit |l#0@@22|)) (=> (U_2_bool (Lit (bool_2_U (_module.__default.Inv _module._default.IndexHi$A@@2 (Lit |l#0@@22|))))) (|_module.__default.ValidPtr#canCall| _module._default.IndexHi$A@@2 (Lit |l#0@@22|) |p#0@@17|))) (=> (U_2_bool (Lit (bool_2_U  (and (_module.__default.Inv _module._default.IndexHi$A@@2 (Lit |l#0@@22|)) (_module.__default.ValidPtr _module._default.IndexHi$A@@2 (Lit |l#0@@22|) |p#0@@17|))))) (_module.DList.DList_q (Lit |l#0@@22|)))) (=> (not (U_2_bool (Lit (bool_2_U  (and (_module.__default.Inv _module._default.IndexHi$A@@2 (Lit |l#0@@22|)) (_module.__default.ValidPtr _module._default.IndexHi$A@@2 (Lit |l#0@@22|) |p#0@@17|)))))) (_module.DList.DList_q (Lit |l#0@@22|)))) (= (_module.__default.IndexHi _module._default.IndexHi$A@@2 (Lit |l#0@@22|) |p#0@@17|) (ite  (and (_module.__default.Inv _module._default.IndexHi$A@@2 (Lit |l#0@@22|)) (_module.__default.ValidPtr _module._default.IndexHi$A@@2 (Lit |l#0@@22|) |p#0@@17|)) (U_2_int ($Unbox intType (|Seq#Index| (Lit (_module.DList.g (Lit |l#0@@22|))) |p#0@@17|))) (|Seq#Length| (Lit (_module.DList.s (Lit |l#0@@22|))))))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1196|
 :pattern ( (_module.__default.IndexHi _module._default.IndexHi$A@@2 (Lit |l#0@@22|) |p#0@@17|))
))))
(assert (forall ((arg0@@250 T@U) (arg1@@117 T@U) (arg2@@70 Int) ) (! (= (type (_module.__default.Get arg0@@250 arg1@@117 arg2@@70)) BoxType)
 :qid |funType:_module.__default.Get|
 :pattern ( (_module.__default.Get arg0@@250 arg1@@117 arg2@@70))
)))
(assert  (=> (<= 19 $FunctionContextHeight) (forall ((_module._default.Get$A T@U) (|l#0@@23| T@U) (|p#0@@18| Int) ) (!  (=> (and (and (= (type _module._default.Get$A) TyType) (= (type |l#0@@23|) DatatypeTypeType)) (or (|_module.__default.Get#canCall| _module._default.Get$A |l#0@@23| |p#0@@18|) (and (not (= 19 $FunctionContextHeight)) (and ($Is |l#0@@23| (Tclass._module.DList _module._default.Get$A)) (and (_module.__default.Inv _module._default.Get$A |l#0@@23|) (_module.__default.ValidPtr _module._default.Get$A |l#0@@23| |p#0@@18|)))))) (and (= (_module.__default.Get _module._default.Get$A |l#0@@23| |p#0@@18|) (|Seq#Index| (_module.__default.Seq _module._default.Get$A |l#0@@23|) (_module.__default.Index _module._default.Get$A |l#0@@23| |p#0@@18|))) ($IsBox (_module.__default.Get _module._default.Get$A |l#0@@23| |p#0@@18|) _module._default.Get$A)))
 :qid |unknown.0:0|
 :skolemid |1199|
 :pattern ( (_module.__default.Get _module._default.Get$A |l#0@@23| |p#0@@18|))
))))
(assert (forall ((_module._default.Get$A@@0 T@U) (|l#0@@24| T@U) (|p#0@@19| Int) ) (!  (=> (and (and (= (type _module._default.Get$A@@0) TyType) (= (type |l#0@@24|) DatatypeTypeType)) ($Is |l#0@@24| (Tclass._module.DList _module._default.Get$A@@0))) (and (=> (|_module.__default.Get#requires| _module._default.Get$A@@0 |l#0@@24| |p#0@@19|) (and (_module.__default.Inv _module._default.Get$A@@0 |l#0@@24|) (_module.__default.ValidPtr _module._default.Get$A@@0 |l#0@@24| |p#0@@19|))) (=> (and (_module.__default.Inv _module._default.Get$A@@0 |l#0@@24|) (_module.__default.ValidPtr _module._default.Get$A@@0 |l#0@@24| |p#0@@19|)) (|_module.__default.Get#requires| _module._default.Get$A@@0 |l#0@@24| |p#0@@19|))))
 :qid |unknown.0:0|
 :skolemid |1200|
 :pattern ( (|_module.__default.Get#requires| _module._default.Get$A@@0 |l#0@@24| |p#0@@19|))
)))
(assert  (=> (<= 19 $FunctionContextHeight) (forall ((_module._default.Get$A@@1 T@U) (|l#0@@25| T@U) (|p#0@@20| Int) ) (!  (=> (and (and (= (type _module._default.Get$A@@1) TyType) (= (type |l#0@@25|) DatatypeTypeType)) (or (|_module.__default.Get#canCall| _module._default.Get$A@@1 |l#0@@25| |p#0@@20|) (and (not (= 19 $FunctionContextHeight)) (and ($Is |l#0@@25| (Tclass._module.DList _module._default.Get$A@@1)) (and (_module.__default.Inv _module._default.Get$A@@1 |l#0@@25|) (_module.__default.ValidPtr _module._default.Get$A@@1 |l#0@@25| |p#0@@20|)))))) (and (and (and (_module.DList.DList_q |l#0@@25|) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Get$A@@1) (_module.DList.nodes |l#0@@25|) |p#0@@20|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Get$A@@1) (_module.DList.nodes |l#0@@25|) |p#0@@20|)))) (= (_module.__default.Get _module._default.Get$A@@1 |l#0@@25| |p#0@@20|) (_module.Option.value (_module.Node.data ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Get$A@@1) (_module.DList.nodes |l#0@@25|) |p#0@@20|)))))))
 :qid |unknown.0:0|
 :skolemid |1201|
 :pattern ( (_module.__default.Get _module._default.Get$A@@1 |l#0@@25| |p#0@@20|))
))))
(assert  (=> (<= 19 $FunctionContextHeight) (forall ((_module._default.Get$A@@2 T@U) (|l#0@@26| T@U) (|p#0@@21| Int) ) (!  (=> (and (and (= (type _module._default.Get$A@@2) TyType) (= (type |l#0@@26|) DatatypeTypeType)) (or (|_module.__default.Get#canCall| _module._default.Get$A@@2 (Lit |l#0@@26|) |p#0@@21|) (and (not (= 19 $FunctionContextHeight)) (and ($Is |l#0@@26| (Tclass._module.DList _module._default.Get$A@@2)) (and (U_2_bool (Lit (bool_2_U (_module.__default.Inv _module._default.Get$A@@2 (Lit |l#0@@26|))))) (U_2_bool (Lit (bool_2_U (_module.__default.ValidPtr _module._default.Get$A@@2 (Lit |l#0@@26|) |p#0@@21|))))))))) (and (and (and (_module.DList.DList_q (Lit |l#0@@26|)) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Get$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@26|))) |p#0@@21|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Get$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@26|))) |p#0@@21|)))) (= (_module.__default.Get _module._default.Get$A@@2 (Lit |l#0@@26|) |p#0@@21|) (_module.Option.value (_module.Node.data ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Get$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@26|))) |p#0@@21|)))))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1202|
 :pattern ( (_module.__default.Get _module._default.Get$A@@2 (Lit |l#0@@26|) |p#0@@21|))
))))
(assert  (=> (<= 20 $FunctionContextHeight) (forall ((_module._default.Next$A T@U) (|l#0@@27| T@U) (|p#0@@22| Int) ) (!  (=> (and (and (= (type _module._default.Next$A) TyType) (= (type |l#0@@27|) DatatypeTypeType)) (or (|_module.__default.Next#canCall| _module._default.Next$A |l#0@@27| |p#0@@22|) (and (not (= 20 $FunctionContextHeight)) (and ($Is |l#0@@27| (Tclass._module.DList _module._default.Next$A)) (and (_module.__default.Inv _module._default.Next$A |l#0@@27|) (_module.__default.MaybePtr _module._default.Next$A |l#0@@27| |p#0@@22|)))))) (and (and (and (and (_module.__default.MaybePtr _module._default.Next$A |l#0@@27| (_module.__default.Next _module._default.Next$A |l#0@@27| |p#0@@22|)) (=> (and (= |p#0@@22| 0) (> (|Seq#Length| (_module.__default.Seq _module._default.Next$A |l#0@@27|)) 0)) (= (_module.__default.Index _module._default.Next$A |l#0@@27| (_module.__default.Next _module._default.Next$A |l#0@@27| |p#0@@22|)) 0))) (=> (and (= |p#0@@22| 0) (= (|Seq#Length| (_module.__default.Seq _module._default.Next$A |l#0@@27|)) 0)) (= (_module.__default.Next _module._default.Next$A |l#0@@27| |p#0@@22|) 0))) (=> (and (not (= |p#0@@22| 0)) (< (_module.__default.Add (_module.__default.Index _module._default.Next$A |l#0@@27| |p#0@@22|) 1) (|Seq#Length| (_module.__default.Seq _module._default.Next$A |l#0@@27|)))) (= (_module.__default.Index _module._default.Next$A |l#0@@27| (_module.__default.Next _module._default.Next$A |l#0@@27| |p#0@@22|)) (_module.__default.Add (_module.__default.Index _module._default.Next$A |l#0@@27| |p#0@@22|) 1)))) (=> (and (not (= |p#0@@22| 0)) (= (_module.__default.Add (_module.__default.Index _module._default.Next$A |l#0@@27| |p#0@@22|) 1) (|Seq#Length| (_module.__default.Seq _module._default.Next$A |l#0@@27|)))) (= (_module.__default.Next _module._default.Next$A |l#0@@27| |p#0@@22|) 0))))
 :qid |unknown.0:0|
 :skolemid |1206|
 :pattern ( (_module.__default.Next _module._default.Next$A |l#0@@27| |p#0@@22|))
))))
(assert (forall ((_module._default.Next$A@@0 T@U) (|l#0@@28| T@U) (|p#0@@23| Int) ) (!  (=> (and (and (= (type _module._default.Next$A@@0) TyType) (= (type |l#0@@28|) DatatypeTypeType)) ($Is |l#0@@28| (Tclass._module.DList _module._default.Next$A@@0))) (and (=> (|_module.__default.Next#requires| _module._default.Next$A@@0 |l#0@@28| |p#0@@23|) (and (_module.__default.Inv _module._default.Next$A@@0 |l#0@@28|) (_module.__default.MaybePtr _module._default.Next$A@@0 |l#0@@28| |p#0@@23|))) (=> (and (_module.__default.Inv _module._default.Next$A@@0 |l#0@@28|) (_module.__default.MaybePtr _module._default.Next$A@@0 |l#0@@28| |p#0@@23|)) (|_module.__default.Next#requires| _module._default.Next$A@@0 |l#0@@28| |p#0@@23|))))
 :qid |unknown.0:0|
 :skolemid |1207|
 :pattern ( (|_module.__default.Next#requires| _module._default.Next$A@@0 |l#0@@28| |p#0@@23|))
)))
(assert  (=> (<= 20 $FunctionContextHeight) (forall ((_module._default.Next$A@@1 T@U) (|l#0@@29| T@U) (|p#0@@24| Int) ) (!  (=> (and (and (= (type _module._default.Next$A@@1) TyType) (= (type |l#0@@29|) DatatypeTypeType)) (or (|_module.__default.Next#canCall| _module._default.Next$A@@1 |l#0@@29| |p#0@@24|) (and (not (= 20 $FunctionContextHeight)) (and ($Is |l#0@@29| (Tclass._module.DList _module._default.Next$A@@1)) (and (_module.__default.Inv _module._default.Next$A@@1 |l#0@@29|) (_module.__default.MaybePtr _module._default.Next$A@@1 |l#0@@29| |p#0@@24|)))))) (and (and (and (_module.DList.DList_q |l#0@@29|) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Next$A@@1) (_module.DList.nodes |l#0@@29|) |p#0@@24|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Next$A@@1) (_module.DList.nodes |l#0@@29|) |p#0@@24|)))) (= (_module.__default.Next _module._default.Next$A@@1 |l#0@@29| |p#0@@24|) (_module.Node.next ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Next$A@@1) (_module.DList.nodes |l#0@@29|) |p#0@@24|))))))
 :qid |unknown.0:0|
 :skolemid |1208|
 :pattern ( (_module.__default.Next _module._default.Next$A@@1 |l#0@@29| |p#0@@24|))
))))
(assert  (=> (<= 20 $FunctionContextHeight) (forall ((_module._default.Next$A@@2 T@U) (|l#0@@30| T@U) (|p#0@@25| Int) ) (!  (=> (and (and (= (type _module._default.Next$A@@2) TyType) (= (type |l#0@@30|) DatatypeTypeType)) (or (|_module.__default.Next#canCall| _module._default.Next$A@@2 (Lit |l#0@@30|) |p#0@@25|) (and (not (= 20 $FunctionContextHeight)) (and ($Is |l#0@@30| (Tclass._module.DList _module._default.Next$A@@2)) (and (U_2_bool (Lit (bool_2_U (_module.__default.Inv _module._default.Next$A@@2 (Lit |l#0@@30|))))) (U_2_bool (Lit (bool_2_U (_module.__default.MaybePtr _module._default.Next$A@@2 (Lit |l#0@@30|) |p#0@@25|))))))))) (and (and (and (_module.DList.DList_q (Lit |l#0@@30|)) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Next$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@30|))) |p#0@@25|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Next$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@30|))) |p#0@@25|)))) (= (_module.__default.Next _module._default.Next$A@@2 (Lit |l#0@@30|) |p#0@@25|) (_module.Node.next ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Next$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@30|))) |p#0@@25|))))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1209|
 :pattern ( (_module.__default.Next _module._default.Next$A@@2 (Lit |l#0@@30|) |p#0@@25|))
))))
(assert  (=> (<= 21 $FunctionContextHeight) (forall ((_module._default.Prev$A T@U) (|l#0@@31| T@U) (|p#0@@26| Int) ) (!  (=> (and (and (= (type _module._default.Prev$A) TyType) (= (type |l#0@@31|) DatatypeTypeType)) (or (|_module.__default.Prev#canCall| _module._default.Prev$A |l#0@@31| |p#0@@26|) (and (not (= 21 $FunctionContextHeight)) (and ($Is |l#0@@31| (Tclass._module.DList _module._default.Prev$A)) (and (_module.__default.Inv _module._default.Prev$A |l#0@@31|) (_module.__default.MaybePtr _module._default.Prev$A |l#0@@31| |p#0@@26|)))))) (and (and (and (and (_module.__default.MaybePtr _module._default.Prev$A |l#0@@31| (_module.__default.Prev _module._default.Prev$A |l#0@@31| |p#0@@26|)) (=> (and (= |p#0@@26| 0) (> (|Seq#Length| (_module.__default.Seq _module._default.Prev$A |l#0@@31|)) 0)) (= (_module.__default.Index _module._default.Prev$A |l#0@@31| (_module.__default.Prev _module._default.Prev$A |l#0@@31| |p#0@@26|)) (_module.__default.Sub (|Seq#Length| (_module.__default.Seq _module._default.Prev$A |l#0@@31|)) 1)))) (=> (and (= |p#0@@26| 0) (= (|Seq#Length| (_module.__default.Seq _module._default.Prev$A |l#0@@31|)) 0)) (= (_module.__default.Prev _module._default.Prev$A |l#0@@31| |p#0@@26|) 0))) (=> (and (not (= |p#0@@26| 0)) (> (_module.__default.Index _module._default.Prev$A |l#0@@31| |p#0@@26|) 0)) (= (_module.__default.Index _module._default.Prev$A |l#0@@31| (_module.__default.Prev _module._default.Prev$A |l#0@@31| |p#0@@26|)) (_module.__default.Sub (_module.__default.Index _module._default.Prev$A |l#0@@31| |p#0@@26|) 1)))) (=> (and (not (= |p#0@@26| 0)) (and (= (_module.__default.Index _module._default.Prev$A |l#0@@31| |p#0@@26|) 0) (= 0 (|Seq#Length| (_module.__default.Seq _module._default.Prev$A |l#0@@31|))))) (= (_module.__default.Prev _module._default.Prev$A |l#0@@31| |p#0@@26|) 0))))
 :qid |unknown.0:0|
 :skolemid |1213|
 :pattern ( (_module.__default.Prev _module._default.Prev$A |l#0@@31| |p#0@@26|))
))))
(assert (forall ((_module._default.Prev$A@@0 T@U) (|l#0@@32| T@U) (|p#0@@27| Int) ) (!  (=> (and (and (= (type _module._default.Prev$A@@0) TyType) (= (type |l#0@@32|) DatatypeTypeType)) ($Is |l#0@@32| (Tclass._module.DList _module._default.Prev$A@@0))) (and (=> (|_module.__default.Prev#requires| _module._default.Prev$A@@0 |l#0@@32| |p#0@@27|) (and (_module.__default.Inv _module._default.Prev$A@@0 |l#0@@32|) (_module.__default.MaybePtr _module._default.Prev$A@@0 |l#0@@32| |p#0@@27|))) (=> (and (_module.__default.Inv _module._default.Prev$A@@0 |l#0@@32|) (_module.__default.MaybePtr _module._default.Prev$A@@0 |l#0@@32| |p#0@@27|)) (|_module.__default.Prev#requires| _module._default.Prev$A@@0 |l#0@@32| |p#0@@27|))))
 :qid |unknown.0:0|
 :skolemid |1214|
 :pattern ( (|_module.__default.Prev#requires| _module._default.Prev$A@@0 |l#0@@32| |p#0@@27|))
)))
(assert  (=> (<= 21 $FunctionContextHeight) (forall ((_module._default.Prev$A@@1 T@U) (|l#0@@33| T@U) (|p#0@@28| Int) ) (!  (=> (and (and (= (type _module._default.Prev$A@@1) TyType) (= (type |l#0@@33|) DatatypeTypeType)) (or (|_module.__default.Prev#canCall| _module._default.Prev$A@@1 |l#0@@33| |p#0@@28|) (and (not (= 21 $FunctionContextHeight)) (and ($Is |l#0@@33| (Tclass._module.DList _module._default.Prev$A@@1)) (and (_module.__default.Inv _module._default.Prev$A@@1 |l#0@@33|) (_module.__default.MaybePtr _module._default.Prev$A@@1 |l#0@@33| |p#0@@28|)))))) (and (and (and (_module.DList.DList_q |l#0@@33|) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Prev$A@@1) (_module.DList.nodes |l#0@@33|) |p#0@@28|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Prev$A@@1) (_module.DList.nodes |l#0@@33|) |p#0@@28|)))) (= (_module.__default.Prev _module._default.Prev$A@@1 |l#0@@33| |p#0@@28|) (_module.Node.prev ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Prev$A@@1) (_module.DList.nodes |l#0@@33|) |p#0@@28|))))))
 :qid |unknown.0:0|
 :skolemid |1215|
 :pattern ( (_module.__default.Prev _module._default.Prev$A@@1 |l#0@@33| |p#0@@28|))
))))
(assert  (=> (<= 21 $FunctionContextHeight) (forall ((_module._default.Prev$A@@2 T@U) (|l#0@@34| T@U) (|p#0@@29| Int) ) (!  (=> (and (and (= (type _module._default.Prev$A@@2) TyType) (= (type |l#0@@34|) DatatypeTypeType)) (or (|_module.__default.Prev#canCall| _module._default.Prev$A@@2 (Lit |l#0@@34|) |p#0@@29|) (and (not (= 21 $FunctionContextHeight)) (and ($Is |l#0@@34| (Tclass._module.DList _module._default.Prev$A@@2)) (and (U_2_bool (Lit (bool_2_U (_module.__default.Inv _module._default.Prev$A@@2 (Lit |l#0@@34|))))) (U_2_bool (Lit (bool_2_U (_module.__default.MaybePtr _module._default.Prev$A@@2 (Lit |l#0@@34|) |p#0@@29|))))))))) (and (and (and (_module.DList.DList_q (Lit |l#0@@34|)) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Prev$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@34|))) |p#0@@29|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Prev$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@34|))) |p#0@@29|)))) (= (_module.__default.Prev _module._default.Prev$A@@2 (Lit |l#0@@34|) |p#0@@29|) (_module.Node.prev ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Prev$A@@2) (Lit (_module.DList.nodes (Lit |l#0@@34|))) |p#0@@29|))))))
 :qid |unknown.0:0|
 :weight 3
 :skolemid |1216|
 :pattern ( (_module.__default.Prev _module._default.Prev$A@@2 (Lit |l#0@@34|) |p#0@@29|))
))))
(assert  (and (and (and (and (and (and (and (forall ((arg0@@251 T@T) (arg1@@118 T@T) ) (! (= (Ctor (MapType6Type arg0@@251 arg1@@118)) 27)
 :qid |ctor:MapType6Type|
)) (forall ((arg0@@252 T@T) (arg1@@119 T@T) ) (! (= (MapType6TypeInv0 (MapType6Type arg0@@252 arg1@@119)) arg0@@252)
 :qid |typeInv:MapType6TypeInv0|
 :pattern ( (MapType6Type arg0@@252 arg1@@119))
))) (forall ((arg0@@253 T@T) (arg1@@120 T@T) ) (! (= (MapType6TypeInv1 (MapType6Type arg0@@253 arg1@@120)) arg1@@120)
 :qid |typeInv:MapType6TypeInv1|
 :pattern ( (MapType6Type arg0@@253 arg1@@120))
))) (forall ((arg0@@254 T@U) (arg1@@121 T@U) (arg2@@71 T@U) ) (! (let ((aVar1@@6 (MapType6TypeInv1 (type arg0@@254))))
(= (type (MapType6Select arg0@@254 arg1@@121 arg2@@71)) aVar1@@6))
 :qid |funType:MapType6Select|
 :pattern ( (MapType6Select arg0@@254 arg1@@121 arg2@@71))
))) (forall ((arg0@@255 T@U) (arg1@@122 T@U) (arg2@@72 T@U) (arg3@@43 T@U) ) (! (let ((aVar1@@7 (type arg3@@43)))
(let ((aVar0@@4 (type arg1@@122)))
(= (type (MapType6Store arg0@@255 arg1@@122 arg2@@72 arg3@@43)) (MapType6Type aVar0@@4 aVar1@@7))))
 :qid |funType:MapType6Store|
 :pattern ( (MapType6Store arg0@@255 arg1@@122 arg2@@72 arg3@@43))
))) (forall ((m@@50 T@U) (x0@@28 T@U) (x1@@22 T@U) (val@@29 T@U) ) (! (let ((aVar1@@8 (MapType6TypeInv1 (type m@@50))))
 (=> (= (type val@@29) aVar1@@8) (= (MapType6Select (MapType6Store m@@50 x0@@28 x1@@22 val@@29) x0@@28 x1@@22) val@@29)))
 :qid |mapAx0:MapType6Select|
 :weight 0
))) (and (and (forall ((val@@30 T@U) (m@@51 T@U) (x0@@29 T@U) (x1@@23 T@U) (y0@@22 T@U) (y1@@18 T@U) ) (!  (or (= x0@@29 y0@@22) (= (MapType6Select (MapType6Store m@@51 x0@@29 x1@@23 val@@30) y0@@22 y1@@18) (MapType6Select m@@51 y0@@22 y1@@18)))
 :qid |mapAx1:MapType6Select:0|
 :weight 0
)) (forall ((val@@31 T@U) (m@@52 T@U) (x0@@30 T@U) (x1@@24 T@U) (y0@@23 T@U) (y1@@19 T@U) ) (!  (or (= x1@@24 y1@@19) (= (MapType6Select (MapType6Store m@@52 x0@@30 x1@@24 val@@31) y0@@23 y1@@19) (MapType6Select m@@52 y0@@23 y1@@19)))
 :qid |mapAx1:MapType6Select:1|
 :weight 0
))) (forall ((val@@32 T@U) (m@@53 T@U) (x0@@31 T@U) (x1@@25 T@U) (y0@@24 T@U) (y1@@20 T@U) ) (!  (or true (= (MapType6Select (MapType6Store m@@53 x0@@31 x1@@25 val@@32) y0@@24 y1@@20) (MapType6Select m@@53 y0@@24 y1@@20)))
 :qid |mapAx2:MapType6Select|
 :weight 0
)))) (forall ((arg0@@256 T@U) (arg1@@123 T@U) (arg2@@73 T@U) (arg3@@44 Bool) ) (! (= (type (|lambda#0| arg0@@256 arg1@@123 arg2@@73 arg3@@44)) (MapType6Type refType boolType))
 :qid |funType:lambda#0|
 :pattern ( (|lambda#0| arg0@@256 arg1@@123 arg2@@73 arg3@@44))
))))
(assert (forall (($o@@9 T@U) ($f T@U) (|l#0@@35| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ) (! (let ((alpha@@6 (FieldTypeInv0 (type $f))))
 (=> (and (and (and (and (= (type $o@@9) refType) (= (type $f) (FieldType alpha@@6))) (= (type |l#0@@35|) refType)) (= (type |l#1|) (MapType0Type refType MapType1Type))) (= (type |l#2|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#0| |l#0@@35| |l#1| |l#2| |l#3|) $o@@9 $f))  (=> (and (not (= $o@@9 |l#0@@35|)) (U_2_bool (MapType1Select (MapType0Select |l#1| $o@@9) |l#2|))) |l#3|))))
 :qid |DLLDafny.11:17|
 :skolemid |1675|
 :pattern ( (MapType6Select (|lambda#0| |l#0@@35| |l#1| |l#2| |l#3|) $o@@9 $f))
)))
(assert (forall ((arg0@@257 T@U) (arg1@@124 T@U) (arg2@@74 T@U) (arg3@@45 Bool) ) (! (= (type (|lambda#1| arg0@@257 arg1@@124 arg2@@74 arg3@@45)) (MapType6Type refType boolType))
 :qid |funType:lambda#1|
 :pattern ( (|lambda#1| arg0@@257 arg1@@124 arg2@@74 arg3@@45))
)))
(assert (forall (($o@@10 T@U) ($f@@0 T@U) (|l#0@@36| T@U) (|l#1@@0| T@U) (|l#2@@0| T@U) (|l#3@@0| Bool) ) (! (let ((alpha@@7 (FieldTypeInv0 (type $f@@0))))
 (=> (and (and (and (and (= (type $o@@10) refType) (= (type $f@@0) (FieldType alpha@@7))) (= (type |l#0@@36|) refType)) (= (type |l#1@@0|) (MapType0Type refType MapType1Type))) (= (type |l#2@@0|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#1| |l#0@@36| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@10 $f@@0))  (=> (and (not (= $o@@10 |l#0@@36|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@0| $o@@10) |l#2@@0|))) |l#3@@0|))))
 :qid |DLLDafny.18:17|
 :skolemid |1676|
 :pattern ( (MapType6Select (|lambda#1| |l#0@@36| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@10 $f@@0))
)))
(assert (forall ((arg0@@258 T@U) (arg1@@125 T@U) (arg2@@75 T@U) (arg3@@46 Bool) ) (! (= (type (|lambda#2| arg0@@258 arg1@@125 arg2@@75 arg3@@46)) (MapType6Type refType boolType))
 :qid |funType:lambda#2|
 :pattern ( (|lambda#2| arg0@@258 arg1@@125 arg2@@75 arg3@@46))
)))
(assert (forall (($o@@11 T@U) ($f@@1 T@U) (|l#0@@37| T@U) (|l#1@@1| T@U) (|l#2@@1| T@U) (|l#3@@1| Bool) ) (! (let ((alpha@@8 (FieldTypeInv0 (type $f@@1))))
 (=> (and (and (and (and (= (type $o@@11) refType) (= (type $f@@1) (FieldType alpha@@8))) (= (type |l#0@@37|) refType)) (= (type |l#1@@1|) (MapType0Type refType MapType1Type))) (= (type |l#2@@1|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#2| |l#0@@37| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@11 $f@@1))  (=> (and (not (= $o@@11 |l#0@@37|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@1| $o@@11) |l#2@@1|))) |l#3@@1|))))
 :qid |DLLDafny.26:17|
 :skolemid |1677|
 :pattern ( (MapType6Select (|lambda#2| |l#0@@37| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@11 $f@@1))
)))
(assert (forall ((arg0@@259 T@U) (arg1@@126 T@U) (arg2@@76 T@U) (arg3@@47 Bool) ) (! (= (type (|lambda#3| arg0@@259 arg1@@126 arg2@@76 arg3@@47)) (MapType6Type refType boolType))
 :qid |funType:lambda#3|
 :pattern ( (|lambda#3| arg0@@259 arg1@@126 arg2@@76 arg3@@47))
)))
(assert (forall (($o@@12 T@U) ($f@@2 T@U) (|l#0@@38| T@U) (|l#1@@2| T@U) (|l#2@@2| T@U) (|l#3@@2| Bool) ) (! (let ((alpha@@9 (FieldTypeInv0 (type $f@@2))))
 (=> (and (and (and (and (= (type $o@@12) refType) (= (type $f@@2) (FieldType alpha@@9))) (= (type |l#0@@38|) refType)) (= (type |l#1@@2|) (MapType0Type refType MapType1Type))) (= (type |l#2@@2|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#3| |l#0@@38| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@12 $f@@2))  (=> (and (not (= $o@@12 |l#0@@38|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@2| $o@@12) |l#2@@2|))) |l#3@@2|))))
 :qid |DLLDafny.34:17|
 :skolemid |1678|
 :pattern ( (MapType6Select (|lambda#3| |l#0@@38| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@12 $f@@2))
)))
(assert (forall ((arg0@@260 T@U) (arg1@@127 T@U) (arg2@@77 T@U) (arg3@@48 Bool) ) (! (= (type (|lambda#4| arg0@@260 arg1@@127 arg2@@77 arg3@@48)) (MapType6Type refType boolType))
 :qid |funType:lambda#4|
 :pattern ( (|lambda#4| arg0@@260 arg1@@127 arg2@@77 arg3@@48))
)))
(assert (forall (($o@@13 T@U) ($f@@3 T@U) (|l#0@@39| T@U) (|l#1@@3| T@U) (|l#2@@3| T@U) (|l#3@@3| Bool) ) (! (let ((alpha@@10 (FieldTypeInv0 (type $f@@3))))
 (=> (and (and (and (and (= (type $o@@13) refType) (= (type $f@@3) (FieldType alpha@@10))) (= (type |l#0@@39|) refType)) (= (type |l#1@@3|) (MapType0Type refType MapType1Type))) (= (type |l#2@@3|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#4| |l#0@@39| |l#1@@3| |l#2@@3| |l#3@@3|) $o@@13 $f@@3))  (=> (and (not (= $o@@13 |l#0@@39|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@3| $o@@13) |l#2@@3|))) |l#3@@3|))))
 :qid |DLLDafny.38:17|
 :skolemid |1679|
 :pattern ( (MapType6Select (|lambda#4| |l#0@@39| |l#1@@3| |l#2@@3| |l#3@@3|) $o@@13 $f@@3))
)))
(assert (forall ((arg0@@261 T@U) (arg1@@128 T@U) (arg2@@78 T@U) (arg3@@49 Bool) ) (! (= (type (|lambda#5| arg0@@261 arg1@@128 arg2@@78 arg3@@49)) (MapType6Type refType boolType))
 :qid |funType:lambda#5|
 :pattern ( (|lambda#5| arg0@@261 arg1@@128 arg2@@78 arg3@@49))
)))
(assert (forall (($o@@14 T@U) ($f@@4 T@U) (|l#0@@40| T@U) (|l#1@@4| T@U) (|l#2@@4| T@U) (|l#3@@4| Bool) ) (! (let ((alpha@@11 (FieldTypeInv0 (type $f@@4))))
 (=> (and (and (and (and (= (type $o@@14) refType) (= (type $f@@4) (FieldType alpha@@11))) (= (type |l#0@@40|) refType)) (= (type |l#1@@4|) (MapType0Type refType MapType1Type))) (= (type |l#2@@4|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#5| |l#0@@40| |l#1@@4| |l#2@@4| |l#3@@4|) $o@@14 $f@@4))  (=> (and (not (= $o@@14 |l#0@@40|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@4| $o@@14) |l#2@@4|))) |l#3@@4|))))
 :qid |DLLDafny.42:56|
 :skolemid |1680|
 :pattern ( (MapType6Select (|lambda#5| |l#0@@40| |l#1@@4| |l#2@@4| |l#3@@4|) $o@@14 $f@@4))
)))
(assert (forall ((arg0@@262 T@U) (arg1@@129 T@U) (arg2@@79 T@U) (arg3@@50 Bool) ) (! (= (type (|lambda#6| arg0@@262 arg1@@129 arg2@@79 arg3@@50)) (MapType6Type refType boolType))
 :qid |funType:lambda#6|
 :pattern ( (|lambda#6| arg0@@262 arg1@@129 arg2@@79 arg3@@50))
)))
(assert (forall (($o@@15 T@U) ($f@@5 T@U) (|l#0@@41| T@U) (|l#1@@5| T@U) (|l#2@@5| T@U) (|l#3@@5| Bool) ) (! (let ((alpha@@12 (FieldTypeInv0 (type $f@@5))))
 (=> (and (and (and (and (= (type $o@@15) refType) (= (type $f@@5) (FieldType alpha@@12))) (= (type |l#0@@41|) refType)) (= (type |l#1@@5|) (MapType0Type refType MapType1Type))) (= (type |l#2@@5|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#6| |l#0@@41| |l#1@@5| |l#2@@5| |l#3@@5|) $o@@15 $f@@5))  (=> (and (not (= $o@@15 |l#0@@41|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@5| $o@@15) |l#2@@5|))) |l#3@@5|))))
 :qid |DLLDafny.45:55|
 :skolemid |1681|
 :pattern ( (MapType6Select (|lambda#6| |l#0@@41| |l#1@@5| |l#2@@5| |l#3@@5|) $o@@15 $f@@5))
)))
(assert (forall ((arg0@@263 T@U) (arg1@@130 T@U) (arg2@@80 T@U) (arg3@@51 Bool) ) (! (= (type (|lambda#7| arg0@@263 arg1@@130 arg2@@80 arg3@@51)) (MapType6Type refType boolType))
 :qid |funType:lambda#7|
 :pattern ( (|lambda#7| arg0@@263 arg1@@130 arg2@@80 arg3@@51))
)))
(assert (forall (($o@@16 T@U) ($f@@6 T@U) (|l#0@@42| T@U) (|l#1@@6| T@U) (|l#2@@6| T@U) (|l#3@@6| Bool) ) (! (let ((alpha@@13 (FieldTypeInv0 (type $f@@6))))
 (=> (and (and (and (and (= (type $o@@16) refType) (= (type $f@@6) (FieldType alpha@@13))) (= (type |l#0@@42|) refType)) (= (type |l#1@@6|) (MapType0Type refType MapType1Type))) (= (type |l#2@@6|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#7| |l#0@@42| |l#1@@6| |l#2@@6| |l#3@@6|) $o@@16 $f@@6))  (=> (and (not (= $o@@16 |l#0@@42|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@6| $o@@16) |l#2@@6|))) |l#3@@6|))))
 :qid |DLLDafny.48:55|
 :skolemid |1682|
 :pattern ( (MapType6Select (|lambda#7| |l#0@@42| |l#1@@6| |l#2@@6| |l#3@@6|) $o@@16 $f@@6))
)))
(assert (forall ((arg0@@264 T@U) (arg1@@131 T@U) (arg2@@81 T@U) (arg3@@52 Bool) ) (! (= (type (|lambda#8| arg0@@264 arg1@@131 arg2@@81 arg3@@52)) (MapType6Type refType boolType))
 :qid |funType:lambda#8|
 :pattern ( (|lambda#8| arg0@@264 arg1@@131 arg2@@81 arg3@@52))
)))
(assert (forall (($o@@17 T@U) ($f@@7 T@U) (|l#0@@43| T@U) (|l#1@@7| T@U) (|l#2@@7| T@U) (|l#3@@7| Bool) ) (! (let ((alpha@@14 (FieldTypeInv0 (type $f@@7))))
 (=> (and (and (and (and (= (type $o@@17) refType) (= (type $f@@7) (FieldType alpha@@14))) (= (type |l#0@@43|) refType)) (= (type |l#1@@7|) (MapType0Type refType MapType1Type))) (= (type |l#2@@7|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#8| |l#0@@43| |l#1@@7| |l#2@@7| |l#3@@7|) $o@@17 $f@@7))  (=> (and (not (= $o@@17 |l#0@@43|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@7| $o@@17) |l#2@@7|))) |l#3@@7|))))
 :qid |DLLDafny.54:57|
 :skolemid |1683|
 :pattern ( (MapType6Select (|lambda#8| |l#0@@43| |l#1@@7| |l#2@@7| |l#3@@7|) $o@@17 $f@@7))
)))
(assert (forall ((arg0@@265 T@U) (arg1@@132 T@U) (arg2@@82 T@U) (arg3@@53 Bool) ) (! (= (type (|lambda#9| arg0@@265 arg1@@132 arg2@@82 arg3@@53)) (MapType6Type refType boolType))
 :qid |funType:lambda#9|
 :pattern ( (|lambda#9| arg0@@265 arg1@@132 arg2@@82 arg3@@53))
)))
(assert (forall (($o@@18 T@U) ($f@@8 T@U) (|l#0@@44| T@U) (|l#1@@8| T@U) (|l#2@@8| T@U) (|l#3@@8| Bool) ) (! (let ((alpha@@15 (FieldTypeInv0 (type $f@@8))))
 (=> (and (and (and (and (= (type $o@@18) refType) (= (type $f@@8) (FieldType alpha@@15))) (= (type |l#0@@44|) refType)) (= (type |l#1@@8|) (MapType0Type refType MapType1Type))) (= (type |l#2@@8|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#9| |l#0@@44| |l#1@@8| |l#2@@8| |l#3@@8|) $o@@18 $f@@8))  (=> (and (not (= $o@@18 |l#0@@44|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@8| $o@@18) |l#2@@8|))) |l#3@@8|))))
 :qid |DLLDafny.57:8|
 :skolemid |1684|
 :pattern ( (MapType6Select (|lambda#9| |l#0@@44| |l#1@@8| |l#2@@8| |l#3@@8|) $o@@18 $f@@8))
)))
(assert (forall ((arg0@@266 T@U) (arg1@@133 T@U) (arg2@@83 T@U) (arg3@@54 Bool) ) (! (= (type (|lambda#10| arg0@@266 arg1@@133 arg2@@83 arg3@@54)) (MapType6Type refType boolType))
 :qid |funType:lambda#10|
 :pattern ( (|lambda#10| arg0@@266 arg1@@133 arg2@@83 arg3@@54))
)))
(assert (forall (($o@@19 T@U) ($f@@9 T@U) (|l#0@@45| T@U) (|l#1@@9| T@U) (|l#2@@9| T@U) (|l#3@@9| Bool) ) (! (let ((alpha@@16 (FieldTypeInv0 (type $f@@9))))
 (=> (and (and (and (and (= (type $o@@19) refType) (= (type $f@@9) (FieldType alpha@@16))) (= (type |l#0@@45|) refType)) (= (type |l#1@@9|) (MapType0Type refType MapType1Type))) (= (type |l#2@@9|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#10| |l#0@@45| |l#1@@9| |l#2@@9| |l#3@@9|) $o@@19 $f@@9))  (=> (and (not (= $o@@19 |l#0@@45|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@9| $o@@19) |l#2@@9|))) |l#3@@9|))))
 :qid |DLLDafny.61:8|
 :skolemid |1685|
 :pattern ( (MapType6Select (|lambda#10| |l#0@@45| |l#1@@9| |l#2@@9| |l#3@@9|) $o@@19 $f@@9))
)))
(assert (forall ((arg0@@267 T@U) (arg1@@134 T@U) (arg2@@84 T@U) (arg3@@55 Bool) ) (! (= (type (|lambda#11| arg0@@267 arg1@@134 arg2@@84 arg3@@55)) (MapType6Type refType boolType))
 :qid |funType:lambda#11|
 :pattern ( (|lambda#11| arg0@@267 arg1@@134 arg2@@84 arg3@@55))
)))
(assert (forall (($o@@20 T@U) ($f@@10 T@U) (|l#0@@46| T@U) (|l#1@@10| T@U) (|l#2@@10| T@U) (|l#3@@10| Bool) ) (! (let ((alpha@@17 (FieldTypeInv0 (type $f@@10))))
 (=> (and (and (and (and (= (type $o@@20) refType) (= (type $f@@10) (FieldType alpha@@17))) (= (type |l#0@@46|) refType)) (= (type |l#1@@10|) (MapType0Type refType MapType1Type))) (= (type |l#2@@10|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#11| |l#0@@46| |l#1@@10| |l#2@@10| |l#3@@10|) $o@@20 $f@@10))  (=> (and (not (= $o@@20 |l#0@@46|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@10| $o@@20) |l#2@@10|))) |l#3@@10|))))
 :qid |DLLDafny.88:11|
 :skolemid |1686|
 :pattern ( (MapType6Select (|lambda#11| |l#0@@46| |l#1@@10| |l#2@@10| |l#3@@10|) $o@@20 $f@@10))
)))
(assert (forall ((arg0@@268 T@U) (arg1@@135 T@U) (arg2@@85 T@U) (arg3@@56 Bool) ) (! (= (type (|lambda#12| arg0@@268 arg1@@135 arg2@@85 arg3@@56)) (MapType6Type refType boolType))
 :qid |funType:lambda#12|
 :pattern ( (|lambda#12| arg0@@268 arg1@@135 arg2@@85 arg3@@56))
)))
(assert (forall (($o@@21 T@U) ($f@@11 T@U) (|l#0@@47| T@U) (|l#1@@11| T@U) (|l#2@@11| T@U) (|l#3@@11| Bool) ) (! (let ((alpha@@18 (FieldTypeInv0 (type $f@@11))))
 (=> (and (and (and (and (= (type $o@@21) refType) (= (type $f@@11) (FieldType alpha@@18))) (= (type |l#0@@47|) refType)) (= (type |l#1@@11|) (MapType0Type refType MapType1Type))) (= (type |l#2@@11|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#12| |l#0@@47| |l#1@@11| |l#2@@11| |l#3@@11|) $o@@21 $f@@11))  (=> (and (not (= $o@@21 |l#0@@47|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@11| $o@@21) |l#2@@11|))) |l#3@@11|))))
 :qid |DLLDafny.88:11|
 :skolemid |1687|
 :pattern ( (MapType6Select (|lambda#12| |l#0@@47| |l#1@@11| |l#2@@11| |l#3@@11|) $o@@21 $f@@11))
)))
(assert (forall ((arg0@@269 T@U) (arg1@@136 T@U) (arg2@@86 T@U) (arg3@@57 Bool) ) (! (= (type (|lambda#13| arg0@@269 arg1@@136 arg2@@86 arg3@@57)) (MapType6Type refType boolType))
 :qid |funType:lambda#13|
 :pattern ( (|lambda#13| arg0@@269 arg1@@136 arg2@@86 arg3@@57))
)))
(assert (forall (($o@@22 T@U) ($f@@12 T@U) (|l#0@@48| T@U) (|l#1@@12| T@U) (|l#2@@12| T@U) (|l#3@@12| Bool) ) (! (let ((alpha@@19 (FieldTypeInv0 (type $f@@12))))
 (=> (and (and (and (and (= (type $o@@22) refType) (= (type $f@@12) (FieldType alpha@@19))) (= (type |l#0@@48|) refType)) (= (type |l#1@@12|) (MapType0Type refType MapType1Type))) (= (type |l#2@@12|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#13| |l#0@@48| |l#1@@12| |l#2@@12| |l#3@@12|) $o@@22 $f@@12))  (=> (and (not (= $o@@22 |l#0@@48|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@12| $o@@22) |l#2@@12|))) |l#3@@12|))))
 :qid |DLLDafny.121:11|
 :skolemid |1688|
 :pattern ( (MapType6Select (|lambda#13| |l#0@@48| |l#1@@12| |l#2@@12| |l#3@@12|) $o@@22 $f@@12))
)))
(assert (forall ((arg0@@270 T@U) (arg1@@137 T@U) (arg2@@87 T@U) (arg3@@58 Bool) ) (! (= (type (|lambda#14| arg0@@270 arg1@@137 arg2@@87 arg3@@58)) (MapType6Type refType boolType))
 :qid |funType:lambda#14|
 :pattern ( (|lambda#14| arg0@@270 arg1@@137 arg2@@87 arg3@@58))
)))
(assert (forall (($o@@23 T@U) ($f@@13 T@U) (|l#0@@49| T@U) (|l#1@@13| T@U) (|l#2@@13| T@U) (|l#3@@13| Bool) ) (! (let ((alpha@@20 (FieldTypeInv0 (type $f@@13))))
 (=> (and (and (and (and (= (type $o@@23) refType) (= (type $f@@13) (FieldType alpha@@20))) (= (type |l#0@@49|) refType)) (= (type |l#1@@13|) (MapType0Type refType MapType1Type))) (= (type |l#2@@13|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#14| |l#0@@49| |l#1@@13| |l#2@@13| |l#3@@13|) $o@@23 $f@@13))  (=> (and (not (= $o@@23 |l#0@@49|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@13| $o@@23) |l#2@@13|))) |l#3@@13|))))
 :qid |DLLDafny.121:11|
 :skolemid |1689|
 :pattern ( (MapType6Select (|lambda#14| |l#0@@49| |l#1@@13| |l#2@@13| |l#3@@13|) $o@@23 $f@@13))
)))
(assert (forall ((arg0@@271 T@U) (arg1@@138 T@U) (arg2@@88 T@U) (arg3@@59 Bool) ) (! (= (type (|lambda#15| arg0@@271 arg1@@138 arg2@@88 arg3@@59)) (MapType6Type refType boolType))
 :qid |funType:lambda#15|
 :pattern ( (|lambda#15| arg0@@271 arg1@@138 arg2@@88 arg3@@59))
)))
(assert (forall (($o@@24 T@U) ($f@@14 T@U) (|l#0@@50| T@U) (|l#1@@14| T@U) (|l#2@@14| T@U) (|l#3@@14| Bool) ) (! (let ((alpha@@21 (FieldTypeInv0 (type $f@@14))))
 (=> (and (and (and (and (= (type $o@@24) refType) (= (type $f@@14) (FieldType alpha@@21))) (= (type |l#0@@50|) refType)) (= (type |l#1@@14|) (MapType0Type refType MapType1Type))) (= (type |l#2@@14|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#15| |l#0@@50| |l#1@@14| |l#2@@14| |l#3@@14|) $o@@24 $f@@14))  (=> (and (not (= $o@@24 |l#0@@50|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@14| $o@@24) |l#2@@14|))) |l#3@@14|))))
 :qid |DLLDafny.131:10|
 :skolemid |1690|
 :pattern ( (MapType6Select (|lambda#15| |l#0@@50| |l#1@@14| |l#2@@14| |l#3@@14|) $o@@24 $f@@14))
)))
(assert (forall ((arg0@@272 T@U) (arg1@@139 T@U) (arg2@@89 T@U) (arg3@@60 Bool) ) (! (= (type (|lambda#16| arg0@@272 arg1@@139 arg2@@89 arg3@@60)) (MapType6Type refType boolType))
 :qid |funType:lambda#16|
 :pattern ( (|lambda#16| arg0@@272 arg1@@139 arg2@@89 arg3@@60))
)))
(assert (forall (($o@@25 T@U) ($f@@15 T@U) (|l#0@@51| T@U) (|l#1@@15| T@U) (|l#2@@15| T@U) (|l#3@@15| Bool) ) (! (let ((alpha@@22 (FieldTypeInv0 (type $f@@15))))
 (=> (and (and (and (and (= (type $o@@25) refType) (= (type $f@@15) (FieldType alpha@@22))) (= (type |l#0@@51|) refType)) (= (type |l#1@@15|) (MapType0Type refType MapType1Type))) (= (type |l#2@@15|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#16| |l#0@@51| |l#1@@15| |l#2@@15| |l#3@@15|) $o@@25 $f@@15))  (=> (and (not (= $o@@25 |l#0@@51|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@15| $o@@25) |l#2@@15|))) |l#3@@15|))))
 :qid |DLLDafny.131:10|
 :skolemid |1691|
 :pattern ( (MapType6Select (|lambda#16| |l#0@@51| |l#1@@15| |l#2@@15| |l#3@@15|) $o@@25 $f@@15))
)))
(assert (forall ((arg0@@273 T@U) (arg1@@140 T@U) (arg2@@90 T@U) (arg3@@61 Bool) ) (! (= (type (|lambda#17| arg0@@273 arg1@@140 arg2@@90 arg3@@61)) (MapType6Type refType boolType))
 :qid |funType:lambda#17|
 :pattern ( (|lambda#17| arg0@@273 arg1@@140 arg2@@90 arg3@@61))
)))
(assert (forall (($o@@26 T@U) ($f@@16 T@U) (|l#0@@52| T@U) (|l#1@@16| T@U) (|l#2@@16| T@U) (|l#3@@16| Bool) ) (! (let ((alpha@@23 (FieldTypeInv0 (type $f@@16))))
 (=> (and (and (and (and (= (type $o@@26) refType) (= (type $f@@16) (FieldType alpha@@23))) (= (type |l#0@@52|) refType)) (= (type |l#1@@16|) (MapType0Type refType MapType1Type))) (= (type |l#2@@16|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#17| |l#0@@52| |l#1@@16| |l#2@@16| |l#3@@16|) $o@@26 $f@@16))  (=> (and (not (= $o@@26 |l#0@@52|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@16| $o@@26) |l#2@@16|))) |l#3@@16|))))
 :qid |DLLDafny.137:11|
 :skolemid |1692|
 :pattern ( (MapType6Select (|lambda#17| |l#0@@52| |l#1@@16| |l#2@@16| |l#3@@16|) $o@@26 $f@@16))
)))
(assert (forall ((arg0@@274 T@U) (arg1@@141 T@U) (arg2@@91 T@U) (arg3@@62 Bool) ) (! (= (type (|lambda#18| arg0@@274 arg1@@141 arg2@@91 arg3@@62)) (MapType6Type refType boolType))
 :qid |funType:lambda#18|
 :pattern ( (|lambda#18| arg0@@274 arg1@@141 arg2@@91 arg3@@62))
)))
(assert (forall (($o@@27 T@U) ($f@@17 T@U) (|l#0@@53| T@U) (|l#1@@17| T@U) (|l#2@@17| T@U) (|l#3@@17| Bool) ) (! (let ((alpha@@24 (FieldTypeInv0 (type $f@@17))))
 (=> (and (and (and (and (= (type $o@@27) refType) (= (type $f@@17) (FieldType alpha@@24))) (= (type |l#0@@53|) refType)) (= (type |l#1@@17|) (MapType0Type refType MapType1Type))) (= (type |l#2@@17|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#18| |l#0@@53| |l#1@@17| |l#2@@17| |l#3@@17|) $o@@27 $f@@17))  (=> (and (not (= $o@@27 |l#0@@53|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@17| $o@@27) |l#2@@17|))) |l#3@@17|))))
 :qid |DLLDafny.137:11|
 :skolemid |1693|
 :pattern ( (MapType6Select (|lambda#18| |l#0@@53| |l#1@@17| |l#2@@17| |l#3@@17|) $o@@27 $f@@17))
)))
(assert (forall ((arg0@@275 T@U) (arg1@@142 T@U) (arg2@@92 T@U) (arg3@@63 Bool) ) (! (= (type (|lambda#19| arg0@@275 arg1@@142 arg2@@92 arg3@@63)) (MapType6Type refType boolType))
 :qid |funType:lambda#19|
 :pattern ( (|lambda#19| arg0@@275 arg1@@142 arg2@@92 arg3@@63))
)))
(assert (forall (($o@@28 T@U) ($f@@18 T@U) (|l#0@@54| T@U) (|l#1@@18| T@U) (|l#2@@18| T@U) (|l#3@@18| Bool) ) (! (let ((alpha@@25 (FieldTypeInv0 (type $f@@18))))
 (=> (and (and (and (and (= (type $o@@28) refType) (= (type $f@@18) (FieldType alpha@@25))) (= (type |l#0@@54|) refType)) (= (type |l#1@@18|) (MapType0Type refType MapType1Type))) (= (type |l#2@@18|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#19| |l#0@@54| |l#1@@18| |l#2@@18| |l#3@@18|) $o@@28 $f@@18))  (=> (and (not (= $o@@28 |l#0@@54|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@18| $o@@28) |l#2@@18|))) |l#3@@18|))))
 :qid |DLLDafny.142:10|
 :skolemid |1694|
 :pattern ( (MapType6Select (|lambda#19| |l#0@@54| |l#1@@18| |l#2@@18| |l#3@@18|) $o@@28 $f@@18))
)))
(assert (forall ((arg0@@276 T@U) (arg1@@143 T@U) (arg2@@93 T@U) (arg3@@64 Bool) ) (! (= (type (|lambda#20| arg0@@276 arg1@@143 arg2@@93 arg3@@64)) (MapType6Type refType boolType))
 :qid |funType:lambda#20|
 :pattern ( (|lambda#20| arg0@@276 arg1@@143 arg2@@93 arg3@@64))
)))
(assert (forall (($o@@29 T@U) ($f@@19 T@U) (|l#0@@55| T@U) (|l#1@@19| T@U) (|l#2@@19| T@U) (|l#3@@19| Bool) ) (! (let ((alpha@@26 (FieldTypeInv0 (type $f@@19))))
 (=> (and (and (and (and (= (type $o@@29) refType) (= (type $f@@19) (FieldType alpha@@26))) (= (type |l#0@@55|) refType)) (= (type |l#1@@19|) (MapType0Type refType MapType1Type))) (= (type |l#2@@19|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#20| |l#0@@55| |l#1@@19| |l#2@@19| |l#3@@19|) $o@@29 $f@@19))  (=> (and (not (= $o@@29 |l#0@@55|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@19| $o@@29) |l#2@@19|))) |l#3@@19|))))
 :qid |DLLDafny.142:10|
 :skolemid |1695|
 :pattern ( (MapType6Select (|lambda#20| |l#0@@55| |l#1@@19| |l#2@@19| |l#3@@19|) $o@@29 $f@@19))
)))
(assert (forall ((arg0@@277 T@U) (arg1@@144 T@U) (arg2@@94 T@U) (arg3@@65 Bool) ) (! (= (type (|lambda#21| arg0@@277 arg1@@144 arg2@@94 arg3@@65)) (MapType6Type refType boolType))
 :qid |funType:lambda#21|
 :pattern ( (|lambda#21| arg0@@277 arg1@@144 arg2@@94 arg3@@65))
)))
(assert (forall (($o@@30 T@U) ($f@@20 T@U) (|l#0@@56| T@U) (|l#1@@20| T@U) (|l#2@@20| T@U) (|l#3@@20| Bool) ) (! (let ((alpha@@27 (FieldTypeInv0 (type $f@@20))))
 (=> (and (and (and (and (= (type $o@@30) refType) (= (type $f@@20) (FieldType alpha@@27))) (= (type |l#0@@56|) refType)) (= (type |l#1@@20|) (MapType0Type refType MapType1Type))) (= (type |l#2@@20|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#21| |l#0@@56| |l#1@@20| |l#2@@20| |l#3@@20|) $o@@30 $f@@20))  (=> (and (not (= $o@@30 |l#0@@56|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@20| $o@@30) |l#2@@20|))) |l#3@@20|))))
 :qid |DLLDafny.149:10|
 :skolemid |1696|
 :pattern ( (MapType6Select (|lambda#21| |l#0@@56| |l#1@@20| |l#2@@20| |l#3@@20|) $o@@30 $f@@20))
)))
(assert (forall ((arg0@@278 T@U) (arg1@@145 T@U) (arg2@@95 T@U) (arg3@@66 Bool) ) (! (= (type (|lambda#22| arg0@@278 arg1@@145 arg2@@95 arg3@@66)) (MapType6Type refType boolType))
 :qid |funType:lambda#22|
 :pattern ( (|lambda#22| arg0@@278 arg1@@145 arg2@@95 arg3@@66))
)))
(assert (forall (($o@@31 T@U) ($f@@21 T@U) (|l#0@@57| T@U) (|l#1@@21| T@U) (|l#2@@21| T@U) (|l#3@@21| Bool) ) (! (let ((alpha@@28 (FieldTypeInv0 (type $f@@21))))
 (=> (and (and (and (and (= (type $o@@31) refType) (= (type $f@@21) (FieldType alpha@@28))) (= (type |l#0@@57|) refType)) (= (type |l#1@@21|) (MapType0Type refType MapType1Type))) (= (type |l#2@@21|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#22| |l#0@@57| |l#1@@21| |l#2@@21| |l#3@@21|) $o@@31 $f@@21))  (=> (and (not (= $o@@31 |l#0@@57|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@21| $o@@31) |l#2@@21|))) |l#3@@21|))))
 :qid |DLLDafny.149:10|
 :skolemid |1697|
 :pattern ( (MapType6Select (|lambda#22| |l#0@@57| |l#1@@21| |l#2@@21| |l#3@@21|) $o@@31 $f@@21))
)))
(assert (forall ((arg0@@279 T@U) (arg1@@146 T@U) (arg2@@96 T@U) (arg3@@67 Bool) ) (! (= (type (|lambda#23| arg0@@279 arg1@@146 arg2@@96 arg3@@67)) (MapType6Type refType boolType))
 :qid |funType:lambda#23|
 :pattern ( (|lambda#23| arg0@@279 arg1@@146 arg2@@96 arg3@@67))
)))
(assert (forall (($o@@32 T@U) ($f@@22 T@U) (|l#0@@58| T@U) (|l#1@@22| T@U) (|l#2@@22| T@U) (|l#3@@22| Bool) ) (! (let ((alpha@@29 (FieldTypeInv0 (type $f@@22))))
 (=> (and (and (and (and (= (type $o@@32) refType) (= (type $f@@22) (FieldType alpha@@29))) (= (type |l#0@@58|) refType)) (= (type |l#1@@22|) (MapType0Type refType MapType1Type))) (= (type |l#2@@22|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#23| |l#0@@58| |l#1@@22| |l#2@@22| |l#3@@22|) $o@@32 $f@@22))  (=> (and (not (= $o@@32 |l#0@@58|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@22| $o@@32) |l#2@@22|))) |l#3@@22|))))
 :qid |DLLDafny.156:17|
 :skolemid |1698|
 :pattern ( (MapType6Select (|lambda#23| |l#0@@58| |l#1@@22| |l#2@@22| |l#3@@22|) $o@@32 $f@@22))
)))
(assert (forall ((arg0@@280 T@U) (arg1@@147 T@U) (arg2@@97 T@U) (arg3@@68 Bool) ) (! (= (type (|lambda#24| arg0@@280 arg1@@147 arg2@@97 arg3@@68)) (MapType6Type refType boolType))
 :qid |funType:lambda#24|
 :pattern ( (|lambda#24| arg0@@280 arg1@@147 arg2@@97 arg3@@68))
)))
(assert (forall (($o@@33 T@U) ($f@@23 T@U) (|l#0@@59| T@U) (|l#1@@23| T@U) (|l#2@@23| T@U) (|l#3@@23| Bool) ) (! (let ((alpha@@30 (FieldTypeInv0 (type $f@@23))))
 (=> (and (and (and (and (= (type $o@@33) refType) (= (type $f@@23) (FieldType alpha@@30))) (= (type |l#0@@59|) refType)) (= (type |l#1@@23|) (MapType0Type refType MapType1Type))) (= (type |l#2@@23|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#24| |l#0@@59| |l#1@@23| |l#2@@23| |l#3@@23|) $o@@33 $f@@23))  (=> (and (not (= $o@@33 |l#0@@59|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@23| $o@@33) |l#2@@23|))) |l#3@@23|))))
 :qid |DLLDafny.156:17|
 :skolemid |1699|
 :pattern ( (MapType6Select (|lambda#24| |l#0@@59| |l#1@@23| |l#2@@23| |l#3@@23|) $o@@33 $f@@23))
)))
(assert (forall ((arg0@@281 T@U) (arg1@@148 T@U) (arg2@@98 T@U) (arg3@@69 Bool) ) (! (= (type (|lambda#25| arg0@@281 arg1@@148 arg2@@98 arg3@@69)) (MapType6Type refType boolType))
 :qid |funType:lambda#25|
 :pattern ( (|lambda#25| arg0@@281 arg1@@148 arg2@@98 arg3@@69))
)))
(assert (forall (($o@@34 T@U) ($f@@24 T@U) (|l#0@@60| T@U) (|l#1@@24| T@U) (|l#2@@24| T@U) (|l#3@@24| Bool) ) (! (let ((alpha@@31 (FieldTypeInv0 (type $f@@24))))
 (=> (and (and (and (and (= (type $o@@34) refType) (= (type $f@@24) (FieldType alpha@@31))) (= (type |l#0@@60|) refType)) (= (type |l#1@@24|) (MapType0Type refType MapType1Type))) (= (type |l#2@@24|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#25| |l#0@@60| |l#1@@24| |l#2@@24| |l#3@@24|) $o@@34 $f@@24))  (=> (and (not (= $o@@34 |l#0@@60|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@24| $o@@34) |l#2@@24|))) |l#3@@24|))))
 :qid |DLLDafny.164:17|
 :skolemid |1700|
 :pattern ( (MapType6Select (|lambda#25| |l#0@@60| |l#1@@24| |l#2@@24| |l#3@@24|) $o@@34 $f@@24))
)))
(assert (forall ((arg0@@282 T@U) (arg1@@149 T@U) (arg2@@99 T@U) (arg3@@70 Bool) ) (! (= (type (|lambda#26| arg0@@282 arg1@@149 arg2@@99 arg3@@70)) (MapType6Type refType boolType))
 :qid |funType:lambda#26|
 :pattern ( (|lambda#26| arg0@@282 arg1@@149 arg2@@99 arg3@@70))
)))
(assert (forall (($o@@35 T@U) ($f@@25 T@U) (|l#0@@61| T@U) (|l#1@@25| T@U) (|l#2@@25| T@U) (|l#3@@25| Bool) ) (! (let ((alpha@@32 (FieldTypeInv0 (type $f@@25))))
 (=> (and (and (and (and (= (type $o@@35) refType) (= (type $f@@25) (FieldType alpha@@32))) (= (type |l#0@@61|) refType)) (= (type |l#1@@25|) (MapType0Type refType MapType1Type))) (= (type |l#2@@25|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#26| |l#0@@61| |l#1@@25| |l#2@@25| |l#3@@25|) $o@@35 $f@@25))  (=> (and (not (= $o@@35 |l#0@@61|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@25| $o@@35) |l#2@@25|))) |l#3@@25|))))
 :qid |DLLDafny.164:17|
 :skolemid |1701|
 :pattern ( (MapType6Select (|lambda#26| |l#0@@61| |l#1@@25| |l#2@@25| |l#3@@25|) $o@@35 $f@@25))
)))
(assert (forall ((arg0@@283 T@U) (arg1@@150 T@U) (arg2@@100 T@U) (arg3@@71 Bool) ) (! (= (type (|lambda#27| arg0@@283 arg1@@150 arg2@@100 arg3@@71)) (MapType6Type refType boolType))
 :qid |funType:lambda#27|
 :pattern ( (|lambda#27| arg0@@283 arg1@@150 arg2@@100 arg3@@71))
)))
(assert (forall (($o@@36 T@U) ($f@@26 T@U) (|l#0@@62| T@U) (|l#1@@26| T@U) (|l#2@@26| T@U) (|l#3@@26| Bool) ) (! (let ((alpha@@33 (FieldTypeInv0 (type $f@@26))))
 (=> (and (and (and (and (= (type $o@@36) refType) (= (type $f@@26) (FieldType alpha@@33))) (= (type |l#0@@62|) refType)) (= (type |l#1@@26|) (MapType0Type refType MapType1Type))) (= (type |l#2@@26|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#27| |l#0@@62| |l#1@@26| |l#2@@26| |l#3@@26|) $o@@36 $f@@26))  (=> (and (not (= $o@@36 |l#0@@62|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@26| $o@@36) |l#2@@26|))) |l#3@@26|))))
 :qid |DLLDafny.176:17|
 :skolemid |1702|
 :pattern ( (MapType6Select (|lambda#27| |l#0@@62| |l#1@@26| |l#2@@26| |l#3@@26|) $o@@36 $f@@26))
)))
(assert (forall ((arg0@@284 T@U) (arg1@@151 T@U) (arg2@@101 T@U) (arg3@@72 Bool) ) (! (= (type (|lambda#28| arg0@@284 arg1@@151 arg2@@101 arg3@@72)) (MapType6Type refType boolType))
 :qid |funType:lambda#28|
 :pattern ( (|lambda#28| arg0@@284 arg1@@151 arg2@@101 arg3@@72))
)))
(assert (forall (($o@@37 T@U) ($f@@27 T@U) (|l#0@@63| T@U) (|l#1@@27| T@U) (|l#2@@27| T@U) (|l#3@@27| Bool) ) (! (let ((alpha@@34 (FieldTypeInv0 (type $f@@27))))
 (=> (and (and (and (and (= (type $o@@37) refType) (= (type $f@@27) (FieldType alpha@@34))) (= (type |l#0@@63|) refType)) (= (type |l#1@@27|) (MapType0Type refType MapType1Type))) (= (type |l#2@@27|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#28| |l#0@@63| |l#1@@27| |l#2@@27| |l#3@@27|) $o@@37 $f@@27))  (=> (and (not (= $o@@37 |l#0@@63|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@27| $o@@37) |l#2@@27|))) |l#3@@27|))))
 :qid |DLLDafny.176:17|
 :skolemid |1703|
 :pattern ( (MapType6Select (|lambda#28| |l#0@@63| |l#1@@27| |l#2@@27| |l#3@@27|) $o@@37 $f@@27))
)))
(assert (forall ((arg0@@285 T@U) (arg1@@152 T@U) (arg2@@102 T@U) (arg3@@73 Bool) ) (! (= (type (|lambda#29| arg0@@285 arg1@@152 arg2@@102 arg3@@73)) (MapType6Type refType boolType))
 :qid |funType:lambda#29|
 :pattern ( (|lambda#29| arg0@@285 arg1@@152 arg2@@102 arg3@@73))
)))
(assert (forall (($o@@38 T@U) ($f@@28 T@U) (|l#0@@64| T@U) (|l#1@@28| T@U) (|l#2@@28| T@U) (|l#3@@28| Bool) ) (! (let ((alpha@@35 (FieldTypeInv0 (type $f@@28))))
 (=> (and (and (and (and (= (type $o@@38) refType) (= (type $f@@28) (FieldType alpha@@35))) (= (type |l#0@@64|) refType)) (= (type |l#1@@28|) (MapType0Type refType MapType1Type))) (= (type |l#2@@28|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#29| |l#0@@64| |l#1@@28| |l#2@@28| |l#3@@28|) $o@@38 $f@@28))  (=> (and (not (= $o@@38 |l#0@@64|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@28| $o@@38) |l#2@@28|))) |l#3@@28|))))
 :qid |DLLDafny.188:8|
 :skolemid |1704|
 :pattern ( (MapType6Select (|lambda#29| |l#0@@64| |l#1@@28| |l#2@@28| |l#3@@28|) $o@@38 $f@@28))
)))
(assert (forall ((arg0@@286 T@U) (arg1@@153 T@U) (arg2@@103 T@U) (arg3@@74 Bool) ) (! (= (type (|lambda#30| arg0@@286 arg1@@153 arg2@@103 arg3@@74)) (MapType6Type refType boolType))
 :qid |funType:lambda#30|
 :pattern ( (|lambda#30| arg0@@286 arg1@@153 arg2@@103 arg3@@74))
)))
(assert (forall (($o@@39 T@U) ($f@@29 T@U) (|l#0@@65| T@U) (|l#1@@29| T@U) (|l#2@@29| T@U) (|l#3@@29| Bool) ) (! (let ((alpha@@36 (FieldTypeInv0 (type $f@@29))))
 (=> (and (and (and (and (= (type $o@@39) refType) (= (type $f@@29) (FieldType alpha@@36))) (= (type |l#0@@65|) refType)) (= (type |l#1@@29|) (MapType0Type refType MapType1Type))) (= (type |l#2@@29|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#30| |l#0@@65| |l#1@@29| |l#2@@29| |l#3@@29|) $o@@39 $f@@29))  (=> (and (not (= $o@@39 |l#0@@65|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@29| $o@@39) |l#2@@29|))) |l#3@@29|))))
 :qid |DLLDafny.188:8|
 :skolemid |1705|
 :pattern ( (MapType6Select (|lambda#30| |l#0@@65| |l#1@@29| |l#2@@29| |l#3@@29|) $o@@39 $f@@29))
)))
(assert (forall ((arg0@@287 T@U) (arg1@@154 T@U) (arg2@@104 T@U) (arg3@@75 Bool) ) (! (= (type (|lambda#31| arg0@@287 arg1@@154 arg2@@104 arg3@@75)) (MapType6Type refType boolType))
 :qid |funType:lambda#31|
 :pattern ( (|lambda#31| arg0@@287 arg1@@154 arg2@@104 arg3@@75))
)))
(assert (forall (($o@@40 T@U) ($f@@30 T@U) (|l#0@@66| T@U) (|l#1@@30| T@U) (|l#2@@30| T@U) (|l#3@@30| Bool) ) (! (let ((alpha@@37 (FieldTypeInv0 (type $f@@30))))
 (=> (and (and (and (and (= (type $o@@40) refType) (= (type $f@@30) (FieldType alpha@@37))) (= (type |l#0@@66|) refType)) (= (type |l#1@@30|) (MapType0Type refType MapType1Type))) (= (type |l#2@@30|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#31| |l#0@@66| |l#1@@30| |l#2@@30| |l#3@@30|) $o@@40 $f@@30))  (=> (and (not (= $o@@40 |l#0@@66|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@30| $o@@40) |l#2@@30|))) |l#3@@30|))))
 :qid |DLLDafny.211:14|
 :skolemid |1706|
 :pattern ( (MapType6Select (|lambda#31| |l#0@@66| |l#1@@30| |l#2@@30| |l#3@@30|) $o@@40 $f@@30))
)))
(assert (forall ((arg0@@288 T@U) (arg1@@155 T@U) (arg2@@105 T@U) (arg3@@76 Bool) ) (! (= (type (|lambda#32| arg0@@288 arg1@@155 arg2@@105 arg3@@76)) (MapType6Type refType boolType))
 :qid |funType:lambda#32|
 :pattern ( (|lambda#32| arg0@@288 arg1@@155 arg2@@105 arg3@@76))
)))
(assert (forall (($o@@41 T@U) ($f@@31 T@U) (|l#0@@67| T@U) (|l#1@@31| T@U) (|l#2@@31| T@U) (|l#3@@31| Bool) ) (! (let ((alpha@@38 (FieldTypeInv0 (type $f@@31))))
 (=> (and (and (and (and (= (type $o@@41) refType) (= (type $f@@31) (FieldType alpha@@38))) (= (type |l#0@@67|) refType)) (= (type |l#1@@31|) (MapType0Type refType MapType1Type))) (= (type |l#2@@31|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#32| |l#0@@67| |l#1@@31| |l#2@@31| |l#3@@31|) $o@@41 $f@@31))  (=> (and (not (= $o@@41 |l#0@@67|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@31| $o@@41) |l#2@@31|))) |l#3@@31|))))
 :qid |DLLDafny.211:14|
 :skolemid |1707|
 :pattern ( (MapType6Select (|lambda#32| |l#0@@67| |l#1@@31| |l#2@@31| |l#3@@31|) $o@@41 $f@@31))
)))
(assert (forall ((arg0@@289 Int) (arg1@@156 Int) (arg2@@106 Int) ) (! (= (type (|lambda#33| arg0@@289 arg1@@156 arg2@@106)) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))
 :qid |funType:lambda#33|
 :pattern ( (|lambda#33| arg0@@289 arg1@@156 arg2@@106))
)))
(assert (forall ((|$l#1#heap#0| T@U) (|$l#1#p#0| T@U) (|l#0@@68| Int) (|l#1@@32| Int) (|l#2@@32| Int) ) (!  (=> (and (= (type |$l#1#heap#0|) (MapType0Type refType MapType1Type)) (= (type |$l#1#p#0|) BoxType)) (= (MapType2Select (|lambda#33| |l#0@@68| |l#1@@32| |l#2@@32|) |$l#1#heap#0| |$l#1#p#0|) ($Box (int_2_U (ite (= (U_2_int ($Unbox intType |$l#1#p#0|)) |l#0@@68|) |l#1@@32| |l#2@@32|)))))
 :qid |DafnyPre.515:12|
 :skolemid |1708|
 :pattern ( (MapType2Select (|lambda#33| |l#0@@68| |l#1@@32| |l#2@@32|) |$l#1#heap#0| |$l#1#p#0|))
)))
(assert (forall ((arg0@@290 T@U) ) (! (= (type (|lambda#34| arg0@@290)) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))
 :qid |funType:lambda#34|
 :pattern ( (|lambda#34| arg0@@290))
)))
(assert (forall ((|$l#1#heap#0@@0| T@U) (|$l#1#p#0@@0| T@U) (|l#0@@69| T@U) ) (!  (=> (and (and (= (type |$l#1#heap#0@@0|) (MapType0Type refType MapType1Type)) (= (type |$l#1#p#0@@0|) BoxType)) (= (type |l#0@@69|) TyType)) (= (U_2_bool (MapType2Select (|lambda#34| |l#0@@69|) |$l#1#heap#0@@0| |$l#1#p#0@@0|)) ($IsBox |$l#1#p#0@@0| |l#0@@69|)))
 :qid |DafnyPre.515:12|
 :skolemid |1709|
 :pattern ( (MapType2Select (|lambda#34| |l#0@@69|) |$l#1#heap#0@@0| |$l#1#p#0@@0|))
)))
(assert (forall ((arg0@@291 Bool) ) (! (= (type (|lambda#35| arg0@@291)) (MapType0Type refType boolType))
 :qid |funType:lambda#35|
 :pattern ( (|lambda#35| arg0@@291))
)))
(assert (forall ((|$l#1#o#0| T@U) (|l#0@@70| Bool) ) (!  (=> (= (type |$l#1#o#0|) refType) (= (U_2_bool (MapType0Select (|lambda#35| |l#0@@70|) |$l#1#o#0|)) |l#0@@70|))
 :qid |unknown.0:0|
 :skolemid |1710|
 :pattern ( (MapType0Select (|lambda#35| |l#0@@70|) |$l#1#o#0|))
)))
(assert (forall ((arg0@@292 T@U) ) (! (= (type (|lambda#36| arg0@@292)) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))
 :qid |funType:lambda#36|
 :pattern ( (|lambda#36| arg0@@292))
)))
(assert (forall ((|$l#1#heap#0@@1| T@U) (|$l#1#p#0@@1| T@U) (|l#0@@71| T@U) ) (!  (=> (and (and (= (type |$l#1#heap#0@@1|) (MapType0Type refType MapType1Type)) (= (type |$l#1#p#0@@1|) BoxType)) (= (type |l#0@@71|) (MapType0Type BoxType boolType))) (= (MapType2Select (|lambda#36| |l#0@@71|) |$l#1#heap#0@@1| |$l#1#p#0@@1|) |l#0@@71|))
 :qid |DafnyPre.515:12|
 :skolemid |1711|
 :pattern ( (MapType2Select (|lambda#36| |l#0@@71|) |$l#1#heap#0@@1| |$l#1#p#0@@1|))
)))
(assert (forall ((arg0@@293 T@U) ) (! (= (type (|lambda#37| arg0@@293)) (MapType0Type LayerTypeType HandleTypeType))
 :qid |funType:lambda#37|
 :pattern ( (|lambda#37| arg0@@293))
)))
(assert (forall ((|$l#1#ly#0| T@U) (|l#0@@72| T@U) ) (!  (=> (and (= (type |$l#1#ly#0|) LayerTypeType) (= (type |l#0@@72|) HandleTypeType)) (= (MapType0Select (|lambda#37| |l#0@@72|) |$l#1#ly#0|) |l#0@@72|))
 :qid |unknown.0:0|
 :skolemid |1712|
 :pattern ( (MapType0Select (|lambda#37| |l#0@@72|) |$l#1#ly#0|))
)))
(assert (forall ((arg0@@294 T@U) (arg1@@157 T@U) (arg2@@107 T@U) (arg3@@77 Bool) ) (! (= (type (|lambda#53| arg0@@294 arg1@@157 arg2@@107 arg3@@77)) (MapType6Type refType boolType))
 :qid |funType:lambda#53|
 :pattern ( (|lambda#53| arg0@@294 arg1@@157 arg2@@107 arg3@@77))
)))
(assert (forall (($o@@42 T@U) ($f@@32 T@U) (|l#0@@73| T@U) (|l#1@@33| T@U) (|l#2@@33| T@U) (|l#3@@32| Bool) ) (! (let ((alpha@@39 (FieldTypeInv0 (type $f@@32))))
 (=> (and (and (and (and (= (type $o@@42) refType) (= (type $f@@32) (FieldType alpha@@39))) (= (type |l#0@@73|) refType)) (= (type |l#1@@33|) (MapType0Type refType MapType1Type))) (= (type |l#2@@33|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#53| |l#0@@73| |l#1@@33| |l#2@@33| |l#3@@32|) $o@@42 $f@@32))  (=> (and (not (= $o@@42 |l#0@@73|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@33| $o@@42) |l#2@@33|))) |l#3@@32|))))
 :qid |DLLDafny.219:23|
 :skolemid |1713|
 :pattern ( (MapType6Select (|lambda#53| |l#0@@73| |l#1@@33| |l#2@@33| |l#3@@32|) $o@@42 $f@@32))
)))
(assert (forall ((arg0@@295 T@U) (arg1@@158 T@U) (arg2@@108 T@U) (arg3@@78 Bool) ) (! (= (type (|lambda#54| arg0@@295 arg1@@158 arg2@@108 arg3@@78)) (MapType6Type refType boolType))
 :qid |funType:lambda#54|
 :pattern ( (|lambda#54| arg0@@295 arg1@@158 arg2@@108 arg3@@78))
)))
(assert (forall (($o@@43 T@U) ($f@@33 T@U) (|l#0@@74| T@U) (|l#1@@34| T@U) (|l#2@@34| T@U) (|l#3@@33| Bool) ) (! (let ((alpha@@40 (FieldTypeInv0 (type $f@@33))))
 (=> (and (and (and (and (= (type $o@@43) refType) (= (type $f@@33) (FieldType alpha@@40))) (= (type |l#0@@74|) refType)) (= (type |l#1@@34|) (MapType0Type refType MapType1Type))) (= (type |l#2@@34|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#54| |l#0@@74| |l#1@@34| |l#2@@34| |l#3@@33|) $o@@43 $f@@33))  (=> (and (not (= $o@@43 |l#0@@74|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@34| $o@@43) |l#2@@34|))) |l#3@@33|))))
 :qid |DLLDafny.223:8|
 :skolemid |1714|
 :pattern ( (MapType6Select (|lambda#54| |l#0@@74| |l#1@@34| |l#2@@34| |l#3@@33|) $o@@43 $f@@33))
)))
(assert (forall ((arg0@@296 T@U) (arg1@@159 T@U) (arg2@@109 T@U) (arg3@@79 Bool) ) (! (= (type (|lambda#55| arg0@@296 arg1@@159 arg2@@109 arg3@@79)) (MapType6Type refType boolType))
 :qid |funType:lambda#55|
 :pattern ( (|lambda#55| arg0@@296 arg1@@159 arg2@@109 arg3@@79))
)))
(assert (forall (($o@@44 T@U) ($f@@34 T@U) (|l#0@@75| T@U) (|l#1@@35| T@U) (|l#2@@35| T@U) (|l#3@@34| Bool) ) (! (let ((alpha@@41 (FieldTypeInv0 (type $f@@34))))
 (=> (and (and (and (and (= (type $o@@44) refType) (= (type $f@@34) (FieldType alpha@@41))) (= (type |l#0@@75|) refType)) (= (type |l#1@@35|) (MapType0Type refType MapType1Type))) (= (type |l#2@@35|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#55| |l#0@@75| |l#1@@35| |l#2@@35| |l#3@@34|) $o@@44 $f@@34))  (=> (and (not (= $o@@44 |l#0@@75|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@35| $o@@44) |l#2@@35|))) |l#3@@34|))))
 :qid |DLLDafny.241:14|
 :skolemid |1715|
 :pattern ( (MapType6Select (|lambda#55| |l#0@@75| |l#1@@35| |l#2@@35| |l#3@@34|) $o@@44 $f@@34))
)))
(assert (forall ((arg0@@297 T@U) (arg1@@160 T@U) (arg2@@110 T@U) (arg3@@80 Bool) ) (! (= (type (|lambda#56| arg0@@297 arg1@@160 arg2@@110 arg3@@80)) (MapType6Type refType boolType))
 :qid |funType:lambda#56|
 :pattern ( (|lambda#56| arg0@@297 arg1@@160 arg2@@110 arg3@@80))
)))
(assert (forall (($o@@45 T@U) ($f@@35 T@U) (|l#0@@76| T@U) (|l#1@@36| T@U) (|l#2@@36| T@U) (|l#3@@35| Bool) ) (! (let ((alpha@@42 (FieldTypeInv0 (type $f@@35))))
 (=> (and (and (and (and (= (type $o@@45) refType) (= (type $f@@35) (FieldType alpha@@42))) (= (type |l#0@@76|) refType)) (= (type |l#1@@36|) (MapType0Type refType MapType1Type))) (= (type |l#2@@36|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#56| |l#0@@76| |l#1@@36| |l#2@@36| |l#3@@35|) $o@@45 $f@@35))  (=> (and (not (= $o@@45 |l#0@@76|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@36| $o@@45) |l#2@@36|))) |l#3@@35|))))
 :qid |DLLDafny.241:14|
 :skolemid |1716|
 :pattern ( (MapType6Select (|lambda#56| |l#0@@76| |l#1@@36| |l#2@@36| |l#3@@35|) $o@@45 $f@@35))
)))
(assert (forall ((arg0@@298 Int) (arg1@@161 T@U) (arg2@@111 Int) ) (! (= (type (|lambda#57| arg0@@298 arg1@@161 arg2@@111)) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))
 :qid |funType:lambda#57|
 :pattern ( (|lambda#57| arg0@@298 arg1@@161 arg2@@111))
)))
(assert (forall ((|$l#1#heap#0@@2| T@U) (|$l#1#x#0| T@U) (|l#0@@77| Int) (|l#1@@37| T@U) (|l#2@@37| Int) ) (!  (=> (and (and (= (type |$l#1#heap#0@@2|) (MapType0Type refType MapType1Type)) (= (type |$l#1#x#0|) BoxType)) (= (type |l#1@@37|) (SeqType BoxType))) (= (MapType2Select (|lambda#57| |l#0@@77| |l#1@@37| |l#2@@37|) |$l#1#heap#0@@2| |$l#1#x#0|) ($Box (int_2_U (ite (< (U_2_int ($Unbox intType |$l#1#x#0|)) |l#0@@77|) (U_2_int ($Unbox intType (|Seq#Index| |l#1@@37| (U_2_int ($Unbox intType |$l#1#x#0|))))) |l#2@@37|)))))
 :qid |DafnyPre.515:12|
 :skolemid |1717|
 :pattern ( (MapType2Select (|lambda#57| |l#0@@77| |l#1@@37| |l#2@@37|) |$l#1#heap#0@@2| |$l#1#x#0|))
)))
(assert (forall ((arg0@@299 T@U) (arg1@@162 Int) (arg2@@112 Int) ) (! (= (type (|lambda#58| arg0@@299 arg1@@162 arg2@@112)) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))
 :qid |funType:lambda#58|
 :pattern ( (|lambda#58| arg0@@299 arg1@@162 arg2@@112))
)))
(assert (forall ((|$l#1#heap#0@@3| T@U) (|$l#1#x#0@@0| T@U) (|l#0@@78| T@U) (|l#1@@38| Int) (|l#2@@38| Int) ) (!  (=> (and (and (= (type |$l#1#heap#0@@3|) (MapType0Type refType MapType1Type)) (= (type |$l#1#x#0@@0|) BoxType)) (= (type |l#0@@78|) TyType)) (= (U_2_bool (MapType2Select (|lambda#58| |l#0@@78| |l#1@@38| |l#2@@38|) |$l#1#heap#0@@3| |$l#1#x#0@@0|))  (and ($IsBox |$l#1#x#0@@0| |l#0@@78|) (and (<= |l#1@@38| (U_2_int ($Unbox intType |$l#1#x#0@@0|))) (< (U_2_int ($Unbox intType |$l#1#x#0@@0|)) |l#2@@38|)))))
 :qid |DafnyPre.515:12|
 :skolemid |1718|
 :pattern ( (MapType2Select (|lambda#58| |l#0@@78| |l#1@@38| |l#2@@38|) |$l#1#heap#0@@3| |$l#1#x#0@@0|))
)))
(assert (forall ((arg0@@300 T@U) (arg1@@163 T@U) (arg2@@113 T@U) (arg3@@81 Bool) ) (! (= (type (|lambda#77| arg0@@300 arg1@@163 arg2@@113 arg3@@81)) (MapType6Type refType boolType))
 :qid |funType:lambda#77|
 :pattern ( (|lambda#77| arg0@@300 arg1@@163 arg2@@113 arg3@@81))
)))
(assert (forall (($o@@46 T@U) ($f@@36 T@U) (|l#0@@79| T@U) (|l#1@@39| T@U) (|l#2@@39| T@U) (|l#3@@36| Bool) ) (! (let ((alpha@@43 (FieldTypeInv0 (type $f@@36))))
 (=> (and (and (and (and (= (type $o@@46) refType) (= (type $f@@36) (FieldType alpha@@43))) (= (type |l#0@@79|) refType)) (= (type |l#1@@39|) (MapType0Type refType MapType1Type))) (= (type |l#2@@39|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#77| |l#0@@79| |l#1@@39| |l#2@@39| |l#3@@36|) $o@@46 $f@@36))  (=> (and (not (= $o@@46 |l#0@@79|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@39| $o@@46) |l#2@@39|))) |l#3@@36|))))
 :qid |DLLDafny.249:28|
 :skolemid |1719|
 :pattern ( (MapType6Select (|lambda#77| |l#0@@79| |l#1@@39| |l#2@@39| |l#3@@36|) $o@@46 $f@@36))
)))
(assert (forall ((arg0@@301 T@U) (arg1@@164 T@U) (arg2@@114 T@U) (arg3@@82 Bool) ) (! (= (type (|lambda#78| arg0@@301 arg1@@164 arg2@@114 arg3@@82)) (MapType6Type refType boolType))
 :qid |funType:lambda#78|
 :pattern ( (|lambda#78| arg0@@301 arg1@@164 arg2@@114 arg3@@82))
)))
(assert (forall (($o@@47 T@U) ($f@@37 T@U) (|l#0@@80| T@U) (|l#1@@40| T@U) (|l#2@@40| T@U) (|l#3@@37| Bool) ) (! (let ((alpha@@44 (FieldTypeInv0 (type $f@@37))))
 (=> (and (and (and (and (= (type $o@@47) refType) (= (type $f@@37) (FieldType alpha@@44))) (= (type |l#0@@80|) refType)) (= (type |l#1@@40|) (MapType0Type refType MapType1Type))) (= (type |l#2@@40|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#78| |l#0@@80| |l#1@@40| |l#2@@40| |l#3@@37|) $o@@47 $f@@37))  (=> (and (not (= $o@@47 |l#0@@80|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@40| $o@@47) |l#2@@40|))) |l#3@@37|))))
 :qid |DLLDafny.254:8|
 :skolemid |1720|
 :pattern ( (MapType6Select (|lambda#78| |l#0@@80| |l#1@@40| |l#2@@40| |l#3@@37|) $o@@47 $f@@37))
)))
(assert (forall ((arg0@@302 T@U) (arg1@@165 T@U) (arg2@@115 T@U) (arg3@@83 Bool) ) (! (= (type (|lambda#79| arg0@@302 arg1@@165 arg2@@115 arg3@@83)) (MapType6Type refType boolType))
 :qid |funType:lambda#79|
 :pattern ( (|lambda#79| arg0@@302 arg1@@165 arg2@@115 arg3@@83))
)))
(assert (forall (($o@@48 T@U) ($f@@38 T@U) (|l#0@@81| T@U) (|l#1@@41| T@U) (|l#2@@41| T@U) (|l#3@@38| Bool) ) (! (let ((alpha@@45 (FieldTypeInv0 (type $f@@38))))
 (=> (and (and (and (and (= (type $o@@48) refType) (= (type $f@@38) (FieldType alpha@@45))) (= (type |l#0@@81|) refType)) (= (type |l#1@@41|) (MapType0Type refType MapType1Type))) (= (type |l#2@@41|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#79| |l#0@@81| |l#1@@41| |l#2@@41| |l#3@@38|) $o@@48 $f@@38))  (=> (and (not (= $o@@48 |l#0@@81|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@41| $o@@48) |l#2@@41|))) |l#3@@38|))))
 :qid |DLLDafny.254:8|
 :skolemid |1721|
 :pattern ( (MapType6Select (|lambda#79| |l#0@@81| |l#1@@41| |l#2@@41| |l#3@@38|) $o@@48 $f@@38))
)))
(assert (forall ((arg0@@303 T@U) (arg1@@166 T@U) (arg2@@116 T@U) (arg3@@84 Bool) ) (! (= (type (|lambda#80| arg0@@303 arg1@@166 arg2@@116 arg3@@84)) (MapType6Type refType boolType))
 :qid |funType:lambda#80|
 :pattern ( (|lambda#80| arg0@@303 arg1@@166 arg2@@116 arg3@@84))
)))
(assert (forall (($o@@49 T@U) ($f@@39 T@U) (|l#0@@82| T@U) (|l#1@@42| T@U) (|l#2@@42| T@U) (|l#3@@39| Bool) ) (! (let ((alpha@@46 (FieldTypeInv0 (type $f@@39))))
 (=> (and (and (and (and (= (type $o@@49) refType) (= (type $f@@39) (FieldType alpha@@46))) (= (type |l#0@@82|) refType)) (= (type |l#1@@42|) (MapType0Type refType MapType1Type))) (= (type |l#2@@42|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#80| |l#0@@82| |l#1@@42| |l#2@@42| |l#3@@39|) $o@@49 $f@@39))  (=> (and (not (= $o@@49 |l#0@@82|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@42| $o@@49) |l#2@@42|))) |l#3@@39|))))
 :qid |DLLDafny.274:14|
 :skolemid |1722|
 :pattern ( (MapType6Select (|lambda#80| |l#0@@82| |l#1@@42| |l#2@@42| |l#3@@39|) $o@@49 $f@@39))
)))
(assert (forall ((arg0@@304 T@U) (arg1@@167 T@U) (arg2@@117 T@U) (arg3@@85 Bool) ) (! (= (type (|lambda#81| arg0@@304 arg1@@167 arg2@@117 arg3@@85)) (MapType6Type refType boolType))
 :qid |funType:lambda#81|
 :pattern ( (|lambda#81| arg0@@304 arg1@@167 arg2@@117 arg3@@85))
)))
(assert (forall (($o@@50 T@U) ($f@@40 T@U) (|l#0@@83| T@U) (|l#1@@43| T@U) (|l#2@@43| T@U) (|l#3@@40| Bool) ) (! (let ((alpha@@47 (FieldTypeInv0 (type $f@@40))))
 (=> (and (and (and (and (= (type $o@@50) refType) (= (type $f@@40) (FieldType alpha@@47))) (= (type |l#0@@83|) refType)) (= (type |l#1@@43|) (MapType0Type refType MapType1Type))) (= (type |l#2@@43|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#81| |l#0@@83| |l#1@@43| |l#2@@43| |l#3@@40|) $o@@50 $f@@40))  (=> (and (not (= $o@@50 |l#0@@83|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@43| $o@@50) |l#2@@43|))) |l#3@@40|))))
 :qid |DLLDafny.274:14|
 :skolemid |1723|
 :pattern ( (MapType6Select (|lambda#81| |l#0@@83| |l#1@@43| |l#2@@43| |l#3@@40|) $o@@50 $f@@40))
)))
(assert (forall ((arg0@@305 T@U) (arg1@@168 Int) (arg2@@118 Int) (arg3@@86 T@U) (arg4@@30 Int) (arg5@@19 T@U) (arg6@@15 Int) (arg7@@4 T@U) ) (! (= (type (|lambda#82| arg0@@305 arg1@@168 arg2@@118 arg3@@86 arg4@@30 arg5@@19 arg6@@15 arg7@@4)) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))
 :qid |funType:lambda#82|
 :pattern ( (|lambda#82| arg0@@305 arg1@@168 arg2@@118 arg3@@86 arg4@@30 arg5@@19 arg6@@15 arg7@@4))
)))
(assert (forall ((|$l#1#heap#0@@4| T@U) (|$l#1#x#0@@1| T@U) (|l#0@@84| T@U) (|l#1@@44| Int) (|l#2@@44| Int) (|l#3@@41| T@U) (|l#4| Int) (|l#5| T@U) (|l#6| Int) (|l#7| T@U) ) (!  (=> (and (and (and (and (and (= (type |$l#1#heap#0@@4|) (MapType0Type refType MapType1Type)) (= (type |$l#1#x#0@@1|) BoxType)) (= (type |l#0@@84|) (SeqType BoxType))) (= (type |l#3@@41|) (SeqType BoxType))) (= (type |l#5|) (SeqType BoxType))) (= (type |l#7|) (SeqType BoxType))) (= (MapType2Select (|lambda#82| |l#0@@84| |l#1@@44| |l#2@@44| |l#3@@41| |l#4| |l#5| |l#6| |l#7|) |$l#1#heap#0@@4| |$l#1#x#0@@1|) ($Box (int_2_U (ite (= (U_2_int ($Unbox intType (|Seq#Index| |l#0@@84| (U_2_int ($Unbox intType |$l#1#x#0@@1|))))) |l#1@@44|) |l#2@@44| (ite (> (U_2_int ($Unbox intType (|Seq#Index| |l#3@@41| (U_2_int ($Unbox intType |$l#1#x#0@@1|))))) |l#4|) (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| |l#5| (U_2_int ($Unbox intType |$l#1#x#0@@1|))))) |l#6|) (U_2_int ($Unbox intType (|Seq#Index| |l#7| (U_2_int ($Unbox intType |$l#1#x#0@@1|)))))))))))
 :qid |DafnyPre.515:12|
 :skolemid |1724|
 :pattern ( (MapType2Select (|lambda#82| |l#0@@84| |l#1@@44| |l#2@@44| |l#3@@41| |l#4| |l#5| |l#6| |l#7|) |$l#1#heap#0@@4| |$l#1#x#0@@1|))
)))
(assert (forall ((arg0@@306 T@U) (arg1@@169 T@U) (arg2@@119 T@U) (arg3@@87 Bool) ) (! (= (type (|lambda#102| arg0@@306 arg1@@169 arg2@@119 arg3@@87)) (MapType6Type refType boolType))
 :qid |funType:lambda#102|
 :pattern ( (|lambda#102| arg0@@306 arg1@@169 arg2@@119 arg3@@87))
)))
(assert (forall (($o@@51 T@U) ($f@@41 T@U) (|l#0@@85| T@U) (|l#1@@45| T@U) (|l#2@@45| T@U) (|l#3@@42| Bool) ) (! (let ((alpha@@48 (FieldTypeInv0 (type $f@@41))))
 (=> (and (and (and (and (= (type $o@@51) refType) (= (type $f@@41) (FieldType alpha@@48))) (= (type |l#0@@85|) refType)) (= (type |l#1@@45|) (MapType0Type refType MapType1Type))) (= (type |l#2@@45|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#102| |l#0@@85| |l#1@@45| |l#2@@45| |l#3@@42|) $o@@51 $f@@41))  (=> (and (not (= $o@@51 |l#0@@85|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@45| $o@@51) |l#2@@45|))) |l#3@@42|))))
 :qid |DLLDafny.282:24|
 :skolemid |1725|
 :pattern ( (MapType6Select (|lambda#102| |l#0@@85| |l#1@@45| |l#2@@45| |l#3@@42|) $o@@51 $f@@41))
)))
(assert (forall ((arg0@@307 T@U) (arg1@@170 T@U) (arg2@@120 T@U) (arg3@@88 Bool) ) (! (= (type (|lambda#103| arg0@@307 arg1@@170 arg2@@120 arg3@@88)) (MapType6Type refType boolType))
 :qid |funType:lambda#103|
 :pattern ( (|lambda#103| arg0@@307 arg1@@170 arg2@@120 arg3@@88))
)))
(assert (forall (($o@@52 T@U) ($f@@42 T@U) (|l#0@@86| T@U) (|l#1@@46| T@U) (|l#2@@46| T@U) (|l#3@@43| Bool) ) (! (let ((alpha@@49 (FieldTypeInv0 (type $f@@42))))
 (=> (and (and (and (and (= (type $o@@52) refType) (= (type $f@@42) (FieldType alpha@@49))) (= (type |l#0@@86|) refType)) (= (type |l#1@@46|) (MapType0Type refType MapType1Type))) (= (type |l#2@@46|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#103| |l#0@@86| |l#1@@46| |l#2@@46| |l#3@@43|) $o@@52 $f@@42))  (=> (and (not (= $o@@52 |l#0@@86|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@46| $o@@52) |l#2@@46|))) |l#3@@43|))))
 :qid |DLLDafny.287:8|
 :skolemid |1726|
 :pattern ( (MapType6Select (|lambda#103| |l#0@@86| |l#1@@46| |l#2@@46| |l#3@@43|) $o@@52 $f@@42))
)))
(assert (forall ((arg0@@308 T@U) (arg1@@171 T@U) (arg2@@121 T@U) (arg3@@89 Bool) ) (! (= (type (|lambda#104| arg0@@308 arg1@@171 arg2@@121 arg3@@89)) (MapType6Type refType boolType))
 :qid |funType:lambda#104|
 :pattern ( (|lambda#104| arg0@@308 arg1@@171 arg2@@121 arg3@@89))
)))
(assert (forall (($o@@53 T@U) ($f@@43 T@U) (|l#0@@87| T@U) (|l#1@@47| T@U) (|l#2@@47| T@U) (|l#3@@44| Bool) ) (! (let ((alpha@@50 (FieldTypeInv0 (type $f@@43))))
 (=> (and (and (and (and (= (type $o@@53) refType) (= (type $f@@43) (FieldType alpha@@50))) (= (type |l#0@@87|) refType)) (= (type |l#1@@47|) (MapType0Type refType MapType1Type))) (= (type |l#2@@47|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#104| |l#0@@87| |l#1@@47| |l#2@@47| |l#3@@44|) $o@@53 $f@@43))  (=> (and (not (= $o@@53 |l#0@@87|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@47| $o@@53) |l#2@@47|))) |l#3@@44|))))
 :qid |DLLDafny.287:8|
 :skolemid |1727|
 :pattern ( (MapType6Select (|lambda#104| |l#0@@87| |l#1@@47| |l#2@@47| |l#3@@44|) $o@@53 $f@@43))
)))
(assert (forall ((arg0@@309 T@U) (arg1@@172 T@U) (arg2@@122 T@U) (arg3@@90 Bool) ) (! (= (type (|lambda#105| arg0@@309 arg1@@172 arg2@@122 arg3@@90)) (MapType6Type refType boolType))
 :qid |funType:lambda#105|
 :pattern ( (|lambda#105| arg0@@309 arg1@@172 arg2@@122 arg3@@90))
)))
(assert (forall (($o@@54 T@U) ($f@@44 T@U) (|l#0@@88| T@U) (|l#1@@48| T@U) (|l#2@@48| T@U) (|l#3@@45| Bool) ) (! (let ((alpha@@51 (FieldTypeInv0 (type $f@@44))))
 (=> (and (and (and (and (= (type $o@@54) refType) (= (type $f@@44) (FieldType alpha@@51))) (= (type |l#0@@88|) refType)) (= (type |l#1@@48|) (MapType0Type refType MapType1Type))) (= (type |l#2@@48|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#105| |l#0@@88| |l#1@@48| |l#2@@48| |l#3@@45|) $o@@54 $f@@44))  (=> (and (not (= $o@@54 |l#0@@88|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@48| $o@@54) |l#2@@48|))) |l#3@@45|))))
 :qid |DLLDafny.313:14|
 :skolemid |1728|
 :pattern ( (MapType6Select (|lambda#105| |l#0@@88| |l#1@@48| |l#2@@48| |l#3@@45|) $o@@54 $f@@44))
)))
(assert (forall ((arg0@@310 T@U) (arg1@@173 T@U) (arg2@@123 T@U) (arg3@@91 Bool) ) (! (= (type (|lambda#106| arg0@@310 arg1@@173 arg2@@123 arg3@@91)) (MapType6Type refType boolType))
 :qid |funType:lambda#106|
 :pattern ( (|lambda#106| arg0@@310 arg1@@173 arg2@@123 arg3@@91))
)))
(assert (forall (($o@@55 T@U) ($f@@45 T@U) (|l#0@@89| T@U) (|l#1@@49| T@U) (|l#2@@49| T@U) (|l#3@@46| Bool) ) (! (let ((alpha@@52 (FieldTypeInv0 (type $f@@45))))
 (=> (and (and (and (and (= (type $o@@55) refType) (= (type $f@@45) (FieldType alpha@@52))) (= (type |l#0@@89|) refType)) (= (type |l#1@@49|) (MapType0Type refType MapType1Type))) (= (type |l#2@@49|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#106| |l#0@@89| |l#1@@49| |l#2@@49| |l#3@@46|) $o@@55 $f@@45))  (=> (and (not (= $o@@55 |l#0@@89|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@49| $o@@55) |l#2@@49|))) |l#3@@46|))))
 :qid |DLLDafny.313:14|
 :skolemid |1729|
 :pattern ( (MapType6Select (|lambda#106| |l#0@@89| |l#1@@49| |l#2@@49| |l#3@@46|) $o@@55 $f@@45))
)))
(assert (forall ((arg0@@311 Int) (arg1@@174 Int) (arg2@@124 Int) (arg3@@92 T@U) (arg4@@31 T@U) (arg5@@20 Int) (arg6@@16 T@U) ) (! (= (type (|lambda#107| arg0@@311 arg1@@174 arg2@@124 arg3@@92 arg4@@31 arg5@@20 arg6@@16)) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))
 :qid |funType:lambda#107|
 :pattern ( (|lambda#107| arg0@@311 arg1@@174 arg2@@124 arg3@@92 arg4@@31 arg5@@20 arg6@@16))
)))
(assert (forall ((|$l#1#heap#0@@5| T@U) (|$l#1#x#0@@2| T@U) (|l#0@@90| Int) (|l#1@@50| Int) (|l#2@@50| Int) (|l#3@@47| T@U) (|l#4@@0| T@U) (|l#5@@0| Int) (|l#6@@0| T@U) ) (!  (=> (and (and (and (and (= (type |$l#1#heap#0@@5|) (MapType0Type refType MapType1Type)) (= (type |$l#1#x#0@@2|) BoxType)) (= (type |l#3@@47|) (SeqType BoxType))) (= (type |l#4@@0|) (SeqType BoxType))) (= (type |l#6@@0|) (SeqType BoxType))) (= (MapType2Select (|lambda#107| |l#0@@90| |l#1@@50| |l#2@@50| |l#3@@47| |l#4@@0| |l#5@@0| |l#6@@0|) |$l#1#heap#0@@5| |$l#1#x#0@@2|) ($Box (int_2_U (ite (= (U_2_int ($Unbox intType |$l#1#x#0@@2|)) |l#0@@90|) |l#1@@50| (ite (< |l#2@@50| (U_2_int ($Unbox intType (|Seq#Index| |l#3@@47| (U_2_int ($Unbox intType |$l#1#x#0@@2|)))))) (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |l#4@@0| (U_2_int ($Unbox intType |$l#1#x#0@@2|))))) |l#5@@0|) (U_2_int ($Unbox intType (|Seq#Index| |l#6@@0| (U_2_int ($Unbox intType |$l#1#x#0@@2|)))))))))))
 :qid |DafnyPre.515:12|
 :skolemid |1730|
 :pattern ( (MapType2Select (|lambda#107| |l#0@@90| |l#1@@50| |l#2@@50| |l#3@@47| |l#4@@0| |l#5@@0| |l#6@@0|) |$l#1#heap#0@@5| |$l#1#x#0@@2|))
)))
(assert (forall ((arg0@@312 T@U) (arg1@@175 T@U) (arg2@@125 T@U) (arg3@@93 Bool) ) (! (= (type (|lambda#127| arg0@@312 arg1@@175 arg2@@125 arg3@@93)) (MapType6Type refType boolType))
 :qid |funType:lambda#127|
 :pattern ( (|lambda#127| arg0@@312 arg1@@175 arg2@@125 arg3@@93))
)))
(assert (forall (($o@@56 T@U) ($f@@46 T@U) (|l#0@@91| T@U) (|l#1@@51| T@U) (|l#2@@51| T@U) (|l#3@@48| Bool) ) (! (let ((alpha@@53 (FieldTypeInv0 (type $f@@46))))
 (=> (and (and (and (and (= (type $o@@56) refType) (= (type $f@@46) (FieldType alpha@@53))) (= (type |l#0@@91|) refType)) (= (type |l#1@@51|) (MapType0Type refType MapType1Type))) (= (type |l#2@@51|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#127| |l#0@@91| |l#1@@51| |l#2@@51| |l#3@@48|) $o@@56 $f@@46))  (=> (and (not (= $o@@56 |l#0@@91|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@51| $o@@56) |l#2@@51|))) |l#3@@48|))))
 :qid |DLLDafny.321:24|
 :skolemid |1731|
 :pattern ( (MapType6Select (|lambda#127| |l#0@@91| |l#1@@51| |l#2@@51| |l#3@@48|) $o@@56 $f@@46))
)))
(assert (forall ((arg0@@313 T@U) (arg1@@176 T@U) (arg2@@126 T@U) (arg3@@94 Bool) ) (! (= (type (|lambda#128| arg0@@313 arg1@@176 arg2@@126 arg3@@94)) (MapType6Type refType boolType))
 :qid |funType:lambda#128|
 :pattern ( (|lambda#128| arg0@@313 arg1@@176 arg2@@126 arg3@@94))
)))
(assert (forall (($o@@57 T@U) ($f@@47 T@U) (|l#0@@92| T@U) (|l#1@@52| T@U) (|l#2@@52| T@U) (|l#3@@49| Bool) ) (! (let ((alpha@@54 (FieldTypeInv0 (type $f@@47))))
 (=> (and (and (and (and (= (type $o@@57) refType) (= (type $f@@47) (FieldType alpha@@54))) (= (type |l#0@@92|) refType)) (= (type |l#1@@52|) (MapType0Type refType MapType1Type))) (= (type |l#2@@52|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#128| |l#0@@92| |l#1@@52| |l#2@@52| |l#3@@49|) $o@@57 $f@@47))  (=> (and (not (= $o@@57 |l#0@@92|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@52| $o@@57) |l#2@@52|))) |l#3@@49|))))
 :qid |DLLDafny.326:8|
 :skolemid |1732|
 :pattern ( (MapType6Select (|lambda#128| |l#0@@92| |l#1@@52| |l#2@@52| |l#3@@49|) $o@@57 $f@@47))
)))
(assert (forall ((arg0@@314 T@U) (arg1@@177 T@U) (arg2@@127 T@U) (arg3@@95 Bool) ) (! (= (type (|lambda#129| arg0@@314 arg1@@177 arg2@@127 arg3@@95)) (MapType6Type refType boolType))
 :qid |funType:lambda#129|
 :pattern ( (|lambda#129| arg0@@314 arg1@@177 arg2@@127 arg3@@95))
)))
(assert (forall (($o@@58 T@U) ($f@@48 T@U) (|l#0@@93| T@U) (|l#1@@53| T@U) (|l#2@@53| T@U) (|l#3@@50| Bool) ) (! (let ((alpha@@55 (FieldTypeInv0 (type $f@@48))))
 (=> (and (and (and (and (= (type $o@@58) refType) (= (type $f@@48) (FieldType alpha@@55))) (= (type |l#0@@93|) refType)) (= (type |l#1@@53|) (MapType0Type refType MapType1Type))) (= (type |l#2@@53|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#129| |l#0@@93| |l#1@@53| |l#2@@53| |l#3@@50|) $o@@58 $f@@48))  (=> (and (not (= $o@@58 |l#0@@93|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@53| $o@@58) |l#2@@53|))) |l#3@@50|))))
 :qid |DLLDafny.326:8|
 :skolemid |1733|
 :pattern ( (MapType6Select (|lambda#129| |l#0@@93| |l#1@@53| |l#2@@53| |l#3@@50|) $o@@58 $f@@48))
)))
(assert (forall ((arg0@@315 T@U) (arg1@@178 T@U) (arg2@@128 T@U) (arg3@@96 Bool) ) (! (= (type (|lambda#130| arg0@@315 arg1@@178 arg2@@128 arg3@@96)) (MapType6Type refType boolType))
 :qid |funType:lambda#130|
 :pattern ( (|lambda#130| arg0@@315 arg1@@178 arg2@@128 arg3@@96))
)))
(assert (forall (($o@@59 T@U) ($f@@49 T@U) (|l#0@@94| T@U) (|l#1@@54| T@U) (|l#2@@54| T@U) (|l#3@@51| Bool) ) (! (let ((alpha@@56 (FieldTypeInv0 (type $f@@49))))
 (=> (and (and (and (and (= (type $o@@59) refType) (= (type $f@@49) (FieldType alpha@@56))) (= (type |l#0@@94|) refType)) (= (type |l#1@@54|) (MapType0Type refType MapType1Type))) (= (type |l#2@@54|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#130| |l#0@@94| |l#1@@54| |l#2@@54| |l#3@@51|) $o@@59 $f@@49))  (=> (and (not (= $o@@59 |l#0@@94|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@54| $o@@59) |l#2@@54|))) |l#3@@51|))))
 :qid |DLLDafny.363:14|
 :skolemid |1734|
 :pattern ( (MapType6Select (|lambda#130| |l#0@@94| |l#1@@54| |l#2@@54| |l#3@@51|) $o@@59 $f@@49))
)))
(assert (forall ((arg0@@316 T@U) (arg1@@179 T@U) (arg2@@129 T@U) (arg3@@97 Bool) ) (! (= (type (|lambda#131| arg0@@316 arg1@@179 arg2@@129 arg3@@97)) (MapType6Type refType boolType))
 :qid |funType:lambda#131|
 :pattern ( (|lambda#131| arg0@@316 arg1@@179 arg2@@129 arg3@@97))
)))
(assert (forall (($o@@60 T@U) ($f@@50 T@U) (|l#0@@95| T@U) (|l#1@@55| T@U) (|l#2@@55| T@U) (|l#3@@52| Bool) ) (! (let ((alpha@@57 (FieldTypeInv0 (type $f@@50))))
 (=> (and (and (and (and (= (type $o@@60) refType) (= (type $f@@50) (FieldType alpha@@57))) (= (type |l#0@@95|) refType)) (= (type |l#1@@55|) (MapType0Type refType MapType1Type))) (= (type |l#2@@55|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#131| |l#0@@95| |l#1@@55| |l#2@@55| |l#3@@52|) $o@@60 $f@@50))  (=> (and (not (= $o@@60 |l#0@@95|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@55| $o@@60) |l#2@@55|))) |l#3@@52|))))
 :qid |DLLDafny.363:14|
 :skolemid |1735|
 :pattern ( (MapType6Select (|lambda#131| |l#0@@95| |l#1@@55| |l#2@@55| |l#3@@52|) $o@@60 $f@@50))
)))
(assert (forall ((arg0@@317 Int) (arg1@@180 Int) (arg2@@130 T@U) (arg3@@98 Int) (arg4@@32 T@U) (arg5@@21 Int) (arg6@@17 T@U) ) (! (= (type (|lambda#132| arg0@@317 arg1@@180 arg2@@130 arg3@@98 arg4@@32 arg5@@21 arg6@@17)) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))
 :qid |funType:lambda#132|
 :pattern ( (|lambda#132| arg0@@317 arg1@@180 arg2@@130 arg3@@98 arg4@@32 arg5@@21 arg6@@17))
)))
(assert (forall ((|$l#1#heap#0@@6| T@U) (|$l#1#x#0@@3| T@U) (|l#0@@96| Int) (|l#1@@56| Int) (|l#2@@56| T@U) (|l#3@@53| Int) (|l#4@@1| T@U) (|l#5@@1| Int) (|l#6@@1| T@U) ) (!  (=> (and (and (and (and (= (type |$l#1#heap#0@@6|) (MapType0Type refType MapType1Type)) (= (type |$l#1#x#0@@3|) BoxType)) (= (type |l#2@@56|) (SeqType BoxType))) (= (type |l#4@@1|) (SeqType BoxType))) (= (type |l#6@@1|) (SeqType BoxType))) (= (MapType2Select (|lambda#132| |l#0@@96| |l#1@@56| |l#2@@56| |l#3@@53| |l#4@@1| |l#5@@1| |l#6@@1|) |$l#1#heap#0@@6| |$l#1#x#0@@3|) ($Box (int_2_U (ite (= (U_2_int ($Unbox intType |$l#1#x#0@@3|)) |l#0@@96|) |l#1@@56| (ite (>= (U_2_int ($Unbox intType (|Seq#Index| |l#2@@56| (U_2_int ($Unbox intType |$l#1#x#0@@3|))))) |l#3@@53|) (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| |l#4@@1| (U_2_int ($Unbox intType |$l#1#x#0@@3|))))) |l#5@@1|) (U_2_int ($Unbox intType (|Seq#Index| |l#6@@1| (U_2_int ($Unbox intType |$l#1#x#0@@3|)))))))))))
 :qid |DafnyPre.515:12|
 :skolemid |1736|
 :pattern ( (MapType2Select (|lambda#132| |l#0@@96| |l#1@@56| |l#2@@56| |l#3@@53| |l#4@@1| |l#5@@1| |l#6@@1|) |$l#1#heap#0@@6| |$l#1#x#0@@3|))
)))
(assert (forall ((arg0@@318 T@U) (arg1@@181 T@U) (arg2@@131 T@U) (arg3@@99 Bool) ) (! (= (type (|lambda#152| arg0@@318 arg1@@181 arg2@@131 arg3@@99)) (MapType6Type refType boolType))
 :qid |funType:lambda#152|
 :pattern ( (|lambda#152| arg0@@318 arg1@@181 arg2@@131 arg3@@99))
)))
(assert (forall (($o@@61 T@U) ($f@@51 T@U) (|l#0@@97| T@U) (|l#1@@57| T@U) (|l#2@@57| T@U) (|l#3@@54| Bool) ) (! (let ((alpha@@58 (FieldTypeInv0 (type $f@@51))))
 (=> (and (and (and (and (= (type $o@@61) refType) (= (type $f@@51) (FieldType alpha@@58))) (= (type |l#0@@97|) refType)) (= (type |l#1@@57|) (MapType0Type refType MapType1Type))) (= (type |l#2@@57|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#152| |l#0@@97| |l#1@@57| |l#2@@57| |l#3@@54|) $o@@61 $f@@51))  (=> (and (not (= $o@@61 |l#0@@97|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@57| $o@@61) |l#2@@57|))) |l#3@@54|))))
 :qid |DLLDafny.371:24|
 :skolemid |1737|
 :pattern ( (MapType6Select (|lambda#152| |l#0@@97| |l#1@@57| |l#2@@57| |l#3@@54|) $o@@61 $f@@51))
)))
(assert (forall ((arg0@@319 T@U) (arg1@@182 T@U) (arg2@@132 T@U) (arg3@@100 Bool) ) (! (= (type (|lambda#153| arg0@@319 arg1@@182 arg2@@132 arg3@@100)) (MapType6Type refType boolType))
 :qid |funType:lambda#153|
 :pattern ( (|lambda#153| arg0@@319 arg1@@182 arg2@@132 arg3@@100))
)))
(assert (forall (($o@@62 T@U) ($f@@52 T@U) (|l#0@@98| T@U) (|l#1@@58| T@U) (|l#2@@58| T@U) (|l#3@@55| Bool) ) (! (let ((alpha@@59 (FieldTypeInv0 (type $f@@52))))
 (=> (and (and (and (and (= (type $o@@62) refType) (= (type $f@@52) (FieldType alpha@@59))) (= (type |l#0@@98|) refType)) (= (type |l#1@@58|) (MapType0Type refType MapType1Type))) (= (type |l#2@@58|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#153| |l#0@@98| |l#1@@58| |l#2@@58| |l#3@@55|) $o@@62 $f@@52))  (=> (and (not (= $o@@62 |l#0@@98|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@58| $o@@62) |l#2@@58|))) |l#3@@55|))))
 :qid |DLLDafny.376:8|
 :skolemid |1738|
 :pattern ( (MapType6Select (|lambda#153| |l#0@@98| |l#1@@58| |l#2@@58| |l#3@@55|) $o@@62 $f@@52))
)))
(assert (forall ((arg0@@320 T@U) (arg1@@183 T@U) (arg2@@133 T@U) (arg3@@101 Bool) ) (! (= (type (|lambda#154| arg0@@320 arg1@@183 arg2@@133 arg3@@101)) (MapType6Type refType boolType))
 :qid |funType:lambda#154|
 :pattern ( (|lambda#154| arg0@@320 arg1@@183 arg2@@133 arg3@@101))
)))
(assert (forall (($o@@63 T@U) ($f@@53 T@U) (|l#0@@99| T@U) (|l#1@@59| T@U) (|l#2@@59| T@U) (|l#3@@56| Bool) ) (! (let ((alpha@@60 (FieldTypeInv0 (type $f@@53))))
 (=> (and (and (and (and (= (type $o@@63) refType) (= (type $f@@53) (FieldType alpha@@60))) (= (type |l#0@@99|) refType)) (= (type |l#1@@59|) (MapType0Type refType MapType1Type))) (= (type |l#2@@59|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#154| |l#0@@99| |l#1@@59| |l#2@@59| |l#3@@56|) $o@@63 $f@@53))  (=> (and (not (= $o@@63 |l#0@@99|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@59| $o@@63) |l#2@@59|))) |l#3@@56|))))
 :qid |DLLDafny.376:8|
 :skolemid |1739|
 :pattern ( (MapType6Select (|lambda#154| |l#0@@99| |l#1@@59| |l#2@@59| |l#3@@56|) $o@@63 $f@@53))
)))
(assert (forall ((arg0@@321 T@U) (arg1@@184 T@U) (arg2@@134 T@U) (arg3@@102 Bool) ) (! (= (type (|lambda#155| arg0@@321 arg1@@184 arg2@@134 arg3@@102)) (MapType6Type refType boolType))
 :qid |funType:lambda#155|
 :pattern ( (|lambda#155| arg0@@321 arg1@@184 arg2@@134 arg3@@102))
)))
(assert (forall (($o@@64 T@U) ($f@@54 T@U) (|l#0@@100| T@U) (|l#1@@60| T@U) (|l#2@@60| T@U) (|l#3@@57| Bool) ) (! (let ((alpha@@61 (FieldTypeInv0 (type $f@@54))))
 (=> (and (and (and (and (= (type $o@@64) refType) (= (type $f@@54) (FieldType alpha@@61))) (= (type |l#0@@100|) refType)) (= (type |l#1@@60|) (MapType0Type refType MapType1Type))) (= (type |l#2@@60|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#155| |l#0@@100| |l#1@@60| |l#2@@60| |l#3@@57|) $o@@64 $f@@54))  (=> (and (not (= $o@@64 |l#0@@100|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@60| $o@@64) |l#2@@60|))) |l#3@@57|))))
 :qid |DLLDafny.409:8|
 :skolemid |1740|
 :pattern ( (MapType6Select (|lambda#155| |l#0@@100| |l#1@@60| |l#2@@60| |l#3@@57|) $o@@64 $f@@54))
)))
(assert (forall ((arg0@@322 T@U) (arg1@@185 T@U) (arg2@@135 T@U) (arg3@@103 Bool) ) (! (= (type (|lambda#156| arg0@@322 arg1@@185 arg2@@135 arg3@@103)) (MapType6Type refType boolType))
 :qid |funType:lambda#156|
 :pattern ( (|lambda#156| arg0@@322 arg1@@185 arg2@@135 arg3@@103))
)))
(assert (forall (($o@@65 T@U) ($f@@55 T@U) (|l#0@@101| T@U) (|l#1@@61| T@U) (|l#2@@61| T@U) (|l#3@@58| Bool) ) (! (let ((alpha@@62 (FieldTypeInv0 (type $f@@55))))
 (=> (and (and (and (and (= (type $o@@65) refType) (= (type $f@@55) (FieldType alpha@@62))) (= (type |l#0@@101|) refType)) (= (type |l#1@@61|) (MapType0Type refType MapType1Type))) (= (type |l#2@@61|) (FieldType boolType))) (= (U_2_bool (MapType6Select (|lambda#156| |l#0@@101| |l#1@@61| |l#2@@61| |l#3@@58|) $o@@65 $f@@55))  (=> (and (not (= $o@@65 |l#0@@101|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@61| $o@@65) |l#2@@61|))) |l#3@@58|))))
 :qid |DLLDafny.419:8|
 :skolemid |1741|
 :pattern ( (MapType6Select (|lambda#156| |l#0@@101| |l#1@@61| |l#2@@61| |l#3@@58|) $o@@65 $f@@55))
)))
(declare-fun $_Frame@0 () T@U)
(declare-fun $Heap@@1 () T@U)
(declare-fun |nodes#0@0| () T@U)
(declare-fun _module._default.Remove$A () T@U)
(declare-fun |s#0@0| () T@U)
(declare-fun |f#0@0| () T@U)
(declare-fun |g#0@0| () T@U)
(declare-fun |let#0#0#0| () T@U)
(declare-fun |l#0@@102| () T@U)
(declare-fun |s'#0@0| () T@U)
(declare-fun |f'#0@0| () T@U)
(declare-fun TType () T@T)
(declare-fun type@@0 (T@U) T@U)
(declare-fun |call4formal@g'#0| () T@U)
(declare-fun $Heap@0 () T@U)
(declare-fun |call4formal@g'#0@0| () T@U)
(declare-fun |node#0@0| () T@U)
(declare-fun |node_prev#0@0| () T@U)
(declare-fun |dt_update_tmp#0#0@0| () T@U)
(declare-fun |let#1#0#0| () T@U)
(declare-fun |##a#1@0| () T@U)
(declare-fun |nodes#0@1| () T@U)
(declare-fun |node_next#0@0| () T@U)
(declare-fun |dt_update_tmp#1#0@0| () T@U)
(declare-fun |let#3#0#0| () T@U)
(declare-fun |##a#2@0| () T@U)
(declare-fun |nodes#0@2| () T@U)
(declare-fun |##a#3@0| () T@U)
(declare-fun |nodes#0@3| () T@U)
(declare-fun |l'#0@0| () T@U)
(declare-fun |l'#0| () T@U)
(declare-fun |s'#0| () T@U)
(declare-fun |f'#0| () T@U)
(declare-fun |g'#0| () T@U)
(declare-fun |$rhs##0| () T@U)
(declare-fun |node#0| () T@U)
(declare-fun |node_prev#0| () T@U)
(declare-fun |node_next#0| () T@U)
(declare-fun %lbl%+0 () Bool)
(declare-fun |freeStack#0@0| () Int)
(declare-fun %lbl%@1 () Bool)
(declare-fun |p#0@@30| () Int)
(declare-fun |index#0@0| () Int)
(declare-fun %lbl%@2 () Bool)
(declare-fun %lbl%@3 () Bool)
(declare-fun %lbl%@4 () Bool)
(declare-fun %lbl%@5 () Bool)
(declare-fun %lbl%@6 () Bool)
(declare-fun $o@@66 () T@U)
(declare-fun $f@@56 () T@U)
(declare-fun $IsHeapAnchor (T@U) Bool)
(declare-fun %lbl%@7 () Bool)
(declare-fun %lbl%@8 () Bool)
(declare-fun |##i#1@0| () Int)
(declare-fun %lbl%@9 () Bool)
(declare-fun %lbl%@10 () Bool)
(declare-fun |let#2#0#0| () Int)
(declare-fun |dt_update#next#0#0@0| () Int)
(declare-fun |##i#2@0| () Int)
(declare-fun %lbl%@11 () Bool)
(declare-fun %lbl%@12 () Bool)
(declare-fun |##i#3@0| () Int)
(declare-fun %lbl%@13 () Bool)
(declare-fun %lbl%@14 () Bool)
(declare-fun |let#4#0#0| () Int)
(declare-fun |dt_update#prev#0#0@0| () Int)
(declare-fun |##i#4@0| () Int)
(declare-fun %lbl%@15 () Bool)
(declare-fun %lbl%@16 () Bool)
(declare-fun %lbl%@17 () Bool)
(declare-fun %lbl%@18 () Bool)
(declare-fun %lbl%@19 () Bool)
(declare-fun %lbl%@20 () Bool)
(declare-fun %lbl%@21 () Bool)
(declare-fun %lbl%@22 () Bool)
(declare-fun %lbl%@23 () Bool)
(declare-fun %lbl%@24 () Bool)
(declare-fun %lbl%@25 () Bool)
(declare-fun %lbl%@26 () Bool)
(declare-fun %lbl%@27 () Bool)
(declare-fun %lbl%@28 () Bool)
(declare-fun %lbl%@29 () Bool)
(declare-fun %lbl%@30 () Bool)
(declare-fun %lbl%@31 () Bool)
(declare-fun %lbl%@32 () Bool)
(declare-fun %lbl%@33 () Bool)
(declare-fun %lbl%@34 () Bool)
(declare-fun %lbl%@35 () Bool)
(declare-fun %lbl%+36 () Bool)
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (type $_Frame@0) (MapType6Type refType boolType)) (= (type $Heap@@1) (MapType0Type refType MapType1Type))) (= (type |nodes#0@0|) (SeqType BoxType))) (= (type _module._default.Remove$A) TyType)) (= (type |s#0@0|) (SeqType BoxType))) (= (type |f#0@0|) (SeqType BoxType))) (= (type |g#0@0|) (SeqType BoxType))) (= (type |let#0#0#0|) DatatypeTypeType)) (= (type |l#0@@102|) DatatypeTypeType)) (= (type |s'#0@0|) (SeqType BoxType))) (= (type |f'#0@0|) (SeqType BoxType))) (= (Ctor TType) 28)) (forall ((arg0@@323 T@U) ) (! (= (type (type@@0 arg0@@323)) TType)
 :qid |funType:type|
 :pattern ( (type@@0 arg0@@323))
))) (= (type |call4formal@g'#0|) (SeqType BoxType))) (= (type $Heap@0) (MapType0Type refType MapType1Type))) (= (type |call4formal@g'#0@0|) (SeqType BoxType))) (= (type |node#0@0|) DatatypeTypeType)) (= (type |node_prev#0@0|) DatatypeTypeType)) (= (type |dt_update_tmp#0#0@0|) DatatypeTypeType)) (= (type |let#1#0#0|) DatatypeTypeType)) (= (type |##a#1@0|) DatatypeTypeType)) (= (type |nodes#0@1|) (SeqType BoxType))) (= (type |node_next#0@0|) DatatypeTypeType)) (= (type |dt_update_tmp#1#0@0|) DatatypeTypeType)) (= (type |let#3#0#0|) DatatypeTypeType)) (= (type |##a#2@0|) DatatypeTypeType)) (= (type |nodes#0@2|) (SeqType BoxType))) (= (type |##a#3@0|) DatatypeTypeType)) (= (type |nodes#0@3|) (SeqType BoxType))) (= (type |l'#0@0|) DatatypeTypeType)) (= (type |l'#0|) DatatypeTypeType)) (= (type |s'#0|) (SeqType BoxType))) (= (type |f'#0|) (SeqType BoxType))) (= (type |g'#0|) (SeqType BoxType))) (= (type |$rhs##0|) (SeqType BoxType))) (= (type |node#0|) DatatypeTypeType)) (= (type |node_prev#0|) DatatypeTypeType)) (= (type |node_next#0|) DatatypeTypeType)))
(push 1)
(set-info :boogie-vc-id Impl$$_module.__default.Remove)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (=> (= $_Frame@0 (|lambda#104| null $Heap@@1 alloc false)) (=> (and (and (and (and ($Is |nodes#0@0| (TSeq (Tclass._module.Node _module._default.Remove$A))) ($IsAlloc |nodes#0@0| (TSeq (Tclass._module.Node _module._default.Remove$A)) $Heap@@1)) (and ($Is |s#0@0| (TSeq _module._default.Remove$A)) ($IsAlloc |s#0@0| (TSeq _module._default.Remove$A) $Heap@@1))) (and (and ($Is |f#0@0| (TSeq TInt)) ($IsAlloc |f#0@0| (TSeq TInt) $Heap@@1)) (and ($Is |g#0@0| (TSeq TInt)) ($IsAlloc |g#0@0| (TSeq TInt) $Heap@@1)))) (and (and (and (= |let#0#0#0| |l#0@@102|) ($Is |let#0#0#0| (Tclass._module.DList _module._default.Remove$A))) (and (_module.DList.DList_q |let#0#0#0|) (_module.DList.DList_q |let#0#0#0|))) (and (and (_module.DList.DList_q |let#0#0#0|) (_module.DList.DList_q |let#0#0#0|)) (and (_module.DList.DList_q |let#0#0#0|) (= (|#_module.DList.DList| |nodes#0@0| |freeStack#0@0| |s#0@0| |f#0@0| |g#0@0|) |let#0#0#0|))))) (and (! (or %lbl%@1  (and (<= 0 |p#0@@30|) (< |p#0@@30| (|Seq#Length| |g#0@0|)))) :lblneg @1) (=> (and (<= 0 |p#0@@30|) (< |p#0@@30| (|Seq#Length| |g#0@0|))) (=> (= |index#0@0| (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |p#0@@30|)))) (=> (and ($IsAlloc |s#0@0| (TSeq _module._default.Remove$A) $Heap@@1) ($IsAlloc (int_2_U |index#0@0|) TInt $Heap@@1)) (and (! (or %lbl%@2 (<= 0 |index#0@0|)) :lblneg @2) (and (! (or %lbl%@3 (< |index#0@0| (|Seq#Length| |s#0@0|))) :lblneg @3) (=> (and (and (and (<= 0 |index#0@0|) (< |index#0@0| (|Seq#Length| |s#0@0|))) (|_module.__default.SeqRemove#canCall| _module._default.Remove$A |s#0@0| |index#0@0|)) (and (and (|_module.__default.SeqRemove#canCall| _module._default.Remove$A |s#0@0| |index#0@0|) (= |s'#0@0| (_module.__default.SeqRemove _module._default.Remove$A |s#0@0| |index#0@0|))) (and ($IsAlloc |f#0@0| (TSeq TInt) $Heap@@1) ($IsAlloc (int_2_U |index#0@0|) TInt $Heap@@1)))) (and (! (or %lbl%@4 (<= 0 |index#0@0|)) :lblneg @4) (and (! (or %lbl%@5 (< |index#0@0| (|Seq#Length| |f#0@0|))) :lblneg @5) (=> (and (and (and (<= 0 |index#0@0|) (< |index#0@0| (|Seq#Length| |f#0@0|))) (|_module.__default.SeqRemove#canCall| TInt |f#0@0| |index#0@0|)) (and (|_module.__default.SeqRemove#canCall| TInt |f#0@0| |index#0@0|) (= |f'#0@0| (_module.__default.SeqRemove TInt |f#0@0| |index#0@0|)))) (and (! (or %lbl%@6 (forall (($o@@67 T@U) ($f@@57 T@U) ) (! (let ((alpha@@63 (FieldTypeInv0 (type $f@@57))))
 (=> (and (and (= (type $o@@67) refType) (= (type $f@@57) (FieldType alpha@@63))) false) (U_2_bool (MapType6Select $_Frame@0 $o@@67 $f@@57))))
 :qid |DLLDafny.303:33|
 :skolemid |1475|
 :no-pattern (type $o@@67)
 :no-pattern (type $f@@57)
 :no-pattern (U_2_int $o@@67)
 :no-pattern (U_2_bool $o@@67)
 :no-pattern (U_2_int $f@@57)
 :no-pattern (U_2_bool $f@@57)
))) :lblneg @6) (=> (forall (($o@@68 T@U) ($f@@58 T@U) ) (! (let ((alpha@@64 (FieldTypeInv0 (type $f@@58))))
 (=> (and (and (= (type $o@@68) refType) (= (type $f@@58) (FieldType alpha@@64))) false) (U_2_bool (MapType6Select $_Frame@0 $o@@68 $f@@58))))
 :qid |DLLDafny.303:33|
 :skolemid |1475|
 :no-pattern (type@@0 $o@@66)
 :no-pattern (type@@0 $f@@56)
 :no-pattern (type $o@@68)
 :no-pattern (type $f@@58)
 :no-pattern (U_2_int $o@@68)
 :no-pattern (U_2_bool $o@@68)
 :no-pattern (U_2_int $f@@58)
 :no-pattern (U_2_bool $f@@58)
)) (=> (and (and ($Is |call4formal@g'#0| (TSeq TInt)) ($IsAlloc |call4formal@g'#0| (TSeq TInt) $Heap@@1)) (and ($IsGoodHeap $Heap@0) ($IsHeapAnchor $Heap@0))) (=> (and (and (and ($Is |call4formal@g'#0@0| (TSeq TInt)) ($IsAlloc |call4formal@g'#0@0| (TSeq TInt) $Heap@0)) (and (= (|Seq#Length| |call4formal@g'#0@0|) (|Seq#Length| |g#0@0|)) (forall ((|x#1| Int) ) (!  (=> (and (<= 0 |x#1|) (< |x#1| (|Seq#Length| |g#0@0|))) (=> (not (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |x#1|))) |index#0@0|)) (=> (< |index#0@0| (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |x#1|)))) (|_module.__default.Sub#canCall| (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |x#1|))) 1))))
 :qid |DLLDafny.276:18|
 :skolemid |1387|
 :pattern ( ($Unbox intType (|Seq#Index| |call4formal@g'#0@0| |x#1|)))
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@0| |x#1|)))
)))) (and (and (forall ((|x#1@@0| Int) ) (!  (=> true (=> (and (<= 0 |x#1@@0|) (< |x#1@@0| (|Seq#Length| |g#0@0|))) (ite (= (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |x#1@@0|))) |index#0@0|) (= (U_2_int ($Unbox intType (|Seq#Index| |call4formal@g'#0@0| |x#1@@0|))) (- 0 2)) (ite (< |index#0@0| (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |x#1@@0|)))) (= (U_2_int ($Unbox intType (|Seq#Index| |call4formal@g'#0@0| |x#1@@0|))) (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |x#1@@0|))) 1)) (= (U_2_int ($Unbox intType (|Seq#Index| |call4formal@g'#0@0| |x#1@@0|))) (U_2_int ($Unbox intType (|Seq#Index| |g#0@0| |x#1@@0|))))))))
 :qid |DLLDafny.276:18|
 :skolemid |1388|
 :pattern ( ($Unbox intType (|Seq#Index| |call4formal@g'#0@0| |x#1@@0|)))
 :pattern ( ($Unbox intType (|Seq#Index| |g#0@0| |x#1@@0|)))
)) (= $Heap@@1 $Heap@0)) (and ($IsAlloc |nodes#0@0| (TSeq (Tclass._module.Node _module._default.Remove$A)) $Heap@0) ($IsAlloc (int_2_U |p#0@@30|) TInt $Heap@0)))) (and (! (or %lbl%@7 (<= 0 |p#0@@30|)) :lblneg @7) (and (! (or %lbl%@8 (< |p#0@@30| (|Seq#Length| |nodes#0@0|))) :lblneg @8) (=> (and (<= 0 |p#0@@30|) (< |p#0@@30| (|Seq#Length| |nodes#0@0|))) (=> (and (and (and (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| |p#0@@30|) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| |p#0@@30|)))) (and (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| |p#0@@30|) (= |node#0@0| ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| |p#0@@30|))))) (and (and (_module.Node.Node_q |node#0@0|) ($IsAlloc |nodes#0@0| (TSeq (Tclass._module.Node _module._default.Remove$A)) $Heap@0)) (and (= |##i#1@0| (_module.Node.prev |node#0@0|)) ($IsAlloc (int_2_U |##i#1@0|) TInt $Heap@0)))) (and (! (or %lbl%@9 (<= 0 |##i#1@0|)) :lblneg @9) (and (! (or %lbl%@10 (< |##i#1@0| (|Seq#Length| |nodes#0@0|))) :lblneg @10) (=> (and (and (and (<= 0 |##i#1@0|) (< |##i#1@0| (|Seq#Length| |nodes#0@0|))) (and (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| (_module.Node.prev |node#0@0|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| (_module.Node.prev |node#0@0|)))))) (and (and (_module.Node.Node_q |node#0@0|) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| (_module.Node.prev |node#0@0|))) (and (= |node_prev#0@0| ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| (_module.Node.prev |node#0@0|)))) (_module.Node.Node_q |node#0@0|)))) (=> (and (and (and (and ($Is |dt_update_tmp#0#0@0| (Tclass._module.Node _module._default.Remove$A)) (= |let#1#0#0| |node_prev#0@0|)) (and ($Is |let#1#0#0| (Tclass._module.Node _module._default.Remove$A)) (= |dt_update_tmp#0#0@0| |let#1#0#0|))) (and (and (_module.Node.Node_q |node#0@0|) (= |let#2#0#0| (_module.Node.next |node#0@0|))) (and (_module.Node.Node_q |node#0@0|) ($Is (int_2_U |let#2#0#0|) TInt)))) (and (and (and (= |dt_update#next#0#0@0| |let#2#0#0|) (_module.Node.Node_q |dt_update_tmp#0#0@0|)) (and (_module.Node.Node_q |dt_update_tmp#0#0@0|) ($IsAlloc |nodes#0@0| (TSeq (Tclass._module.Node _module._default.Remove$A)) $Heap@0))) (and (and (= |##i#2@0| (_module.Node.prev |node#0@0|)) ($IsAlloc (int_2_U |##i#2@0|) TInt $Heap@0)) (and (= |##a#1@0| (let ((|dt_update_tmp#0#1| |node_prev#0@0|))
(let ((|dt_update#next#0#1| (_module.Node.next |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#0#1|) |dt_update#next#0#1| (_module.Node.prev |dt_update_tmp#0#1|))))) ($IsAlloc |##a#1@0| (Tclass._module.Node _module._default.Remove$A) $Heap@0))))) (and (! (or %lbl%@11 (<= 0 |##i#2@0|)) :lblneg @11) (and (! (or %lbl%@12 (< |##i#2@0| (|Seq#Length| |nodes#0@0|))) :lblneg @12) (=> (and (and (<= 0 |##i#2@0|) (< |##i#2@0| (|Seq#Length| |nodes#0@0|))) (|_module.__default.seq__set#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| (_module.Node.prev |node#0@0|) ($Box (let ((|dt_update_tmp#0#1@@0| |node_prev#0@0|))
(let ((|dt_update#next#0#1@@0| (_module.Node.next |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#0#1@@0|) |dt_update#next#0#1@@0| (_module.Node.prev |dt_update_tmp#0#1@@0|))))))) (=> (and (and (and (and (_module.Node.Node_q |node#0@0|) (let ((|dt_update_tmp#0#1@@1| |node_prev#0@0|))
 (and (_module.Node.Node_q |node#0@0|) (and (_module.Node.Node_q |dt_update_tmp#0#1@@1|) (_module.Node.Node_q |dt_update_tmp#0#1@@1|))))) (|_module.__default.seq__set#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| (_module.Node.prev |node#0@0|) ($Box (let ((|dt_update_tmp#0#1@@2| |node_prev#0@0|))
(let ((|dt_update#next#0#1@@1| (_module.Node.next |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#0#1@@2|) |dt_update#next#0#1@@1| (_module.Node.prev |dt_update_tmp#0#1@@2|))))))) (= |nodes#0@1| (_module.__default.seq__set (Tclass._module.Node _module._default.Remove$A) |nodes#0@0| (_module.Node.prev |node#0@0|) ($Box (let ((|dt_update_tmp#0#1@@3| |node_prev#0@0|))
(let ((|dt_update#next#0#1@@2| (_module.Node.next |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#0#1@@3|) |dt_update#next#0#1@@2| (_module.Node.prev |dt_update_tmp#0#1@@3|)))))))) (and (and (_module.Node.Node_q |node#0@0|) ($IsAlloc |nodes#0@1| (TSeq (Tclass._module.Node _module._default.Remove$A)) $Heap@0)) (and (= |##i#3@0| (_module.Node.next |node#0@0|)) ($IsAlloc (int_2_U |##i#3@0|) TInt $Heap@0)))) (and (! (or %lbl%@13 (<= 0 |##i#3@0|)) :lblneg @13) (and (! (or %lbl%@14 (< |##i#3@0| (|Seq#Length| |nodes#0@1|))) :lblneg @14) (=> (and (and (and (<= 0 |##i#3@0|) (< |##i#3@0| (|Seq#Length| |nodes#0@1|))) (and (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@1| (_module.Node.next |node#0@0|)) (_module.Node.Node_q ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Remove$A) |nodes#0@1| (_module.Node.next |node#0@0|)))))) (and (and (_module.Node.Node_q |node#0@0|) (|_module.__default.seq__get#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@1| (_module.Node.next |node#0@0|))) (and (= |node_next#0@0| ($Unbox DatatypeTypeType (_module.__default.seq__get (Tclass._module.Node _module._default.Remove$A) |nodes#0@1| (_module.Node.next |node#0@0|)))) (_module.Node.Node_q |node#0@0|)))) (=> (and (and (and (and ($Is |dt_update_tmp#1#0@0| (Tclass._module.Node _module._default.Remove$A)) (= |let#3#0#0| |node_next#0@0|)) (and ($Is |let#3#0#0| (Tclass._module.Node _module._default.Remove$A)) (= |dt_update_tmp#1#0@0| |let#3#0#0|))) (and (and (_module.Node.Node_q |node#0@0|) (= |let#4#0#0| (_module.Node.prev |node#0@0|))) (and (_module.Node.Node_q |node#0@0|) ($Is (int_2_U |let#4#0#0|) TInt)))) (and (and (and (= |dt_update#prev#0#0@0| |let#4#0#0|) (_module.Node.Node_q |dt_update_tmp#1#0@0|)) (and (_module.Node.Node_q |dt_update_tmp#1#0@0|) ($IsAlloc |nodes#0@1| (TSeq (Tclass._module.Node _module._default.Remove$A)) $Heap@0))) (and (and (= |##i#4@0| (_module.Node.next |node#0@0|)) ($IsAlloc (int_2_U |##i#4@0|) TInt $Heap@0)) (and (= |##a#2@0| (let ((|dt_update_tmp#1#1| |node_next#0@0|))
(let ((|dt_update#prev#0#1| (_module.Node.prev |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#1#1|) (_module.Node.next |dt_update_tmp#1#1|) |dt_update#prev#0#1|)))) ($IsAlloc |##a#2@0| (Tclass._module.Node _module._default.Remove$A) $Heap@0))))) (and (! (or %lbl%@15 (<= 0 |##i#4@0|)) :lblneg @15) (and (! (or %lbl%@16 (< |##i#4@0| (|Seq#Length| |nodes#0@1|))) :lblneg @16) (=> (and (and (<= 0 |##i#4@0|) (< |##i#4@0| (|Seq#Length| |nodes#0@1|))) (|_module.__default.seq__set#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@1| (_module.Node.next |node#0@0|) ($Box (let ((|dt_update_tmp#1#1@@0| |node_next#0@0|))
(let ((|dt_update#prev#0#1@@0| (_module.Node.prev |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#1#1@@0|) (_module.Node.next |dt_update_tmp#1#1@@0|) |dt_update#prev#0#1@@0|)))))) (=> (and (and (and (and (_module.Node.Node_q |node#0@0|) (let ((|dt_update_tmp#1#1@@1| |node_next#0@0|))
 (and (_module.Node.Node_q |node#0@0|) (and (_module.Node.Node_q |dt_update_tmp#1#1@@1|) (_module.Node.Node_q |dt_update_tmp#1#1@@1|))))) (|_module.__default.seq__set#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@1| (_module.Node.next |node#0@0|) ($Box (let ((|dt_update_tmp#1#1@@2| |node_next#0@0|))
(let ((|dt_update#prev#0#1@@1| (_module.Node.prev |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#1#1@@2|) (_module.Node.next |dt_update_tmp#1#1@@2|) |dt_update#prev#0#1@@1|)))))) (= |nodes#0@2| (_module.__default.seq__set (Tclass._module.Node _module._default.Remove$A) |nodes#0@1| (_module.Node.next |node#0@0|) ($Box (let ((|dt_update_tmp#1#1@@3| |node_next#0@0|))
(let ((|dt_update#prev#0#1@@2| (_module.Node.prev |node#0@0|)))
(|#_module.Node.Node| (_module.Node.data |dt_update_tmp#1#1@@3|) (_module.Node.next |dt_update_tmp#1#1@@3|) |dt_update#prev#0#1@@2|))))))) (and (and ($IsAlloc |nodes#0@2| (TSeq (Tclass._module.Node _module._default.Remove$A)) $Heap@0) ($IsAlloc (int_2_U |p#0@@30|) TInt $Heap@0)) (and (= |##a#3@0| (|#_module.Node.Node| (Lit |#_module.Option.None|) |freeStack#0@0| 0)) ($IsAlloc |##a#3@0| (Tclass._module.Node _module._default.Remove$A) $Heap@0)))) (and (! (or %lbl%@17 (<= 0 |p#0@@30|)) :lblneg @17) (and (! (or %lbl%@18 (< |p#0@@30| (|Seq#Length| |nodes#0@2|))) :lblneg @18) (=> (and (<= 0 |p#0@@30|) (< |p#0@@30| (|Seq#Length| |nodes#0@2|))) (=> (and (and (|_module.__default.seq__set#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@2| |p#0@@30| ($Box (|#_module.Node.Node| (Lit |#_module.Option.None|) |freeStack#0@0| 0))) (|_module.__default.seq__set#canCall| (Tclass._module.Node _module._default.Remove$A) |nodes#0@2| |p#0@@30| ($Box (|#_module.Node.Node| (Lit |#_module.Option.None|) |freeStack#0@0| 0)))) (and (= |nodes#0@3| (_module.__default.seq__set (Tclass._module.Node _module._default.Remove$A) |nodes#0@2| |p#0@@30| ($Box (|#_module.Node.Node| (Lit |#_module.Option.None|) |freeStack#0@0| 0)))) (= |l'#0@0| (|#_module.DList.DList| |nodes#0@3| |p#0@@30| |s'#0@0| |f'#0@0| |call4formal@g'#0@0|)))) (and (! (or %lbl%@19  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (= (|Seq#Length| (_module.DList.f |l'#0@0|)) (|Seq#Length| (_module.DList.s |l'#0@0|)))))))) :lblneg @19) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (= (|Seq#Length| (_module.DList.f |l'#0@0|)) (|Seq#Length| (_module.DList.s |l'#0@0|))))))) (and (! (or %lbl%@20  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (= (|Seq#Length| (_module.DList.g |l'#0@0|)) (|Seq#Length| (_module.DList.nodes |l'#0@0|)))))))) :lblneg @20) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (= (|Seq#Length| (_module.DList.g |l'#0@0|)) (|Seq#Length| (_module.DList.nodes |l'#0@0|))))))) (and (! (or %lbl%@21  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (> (|Seq#Length| (_module.DList.nodes |l'#0@0|)) 0)))))) :lblneg @21) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (> (|Seq#Length| (_module.DList.nodes |l'#0@0|)) 0))))) (and (! (or %lbl%@22  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) 0))) (- 0 1))))))) :lblneg @22) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) 0))) (- 0 1)))))) (and (! (or %lbl%@23  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (<= 0 (_module.DList.freeStack |l'#0@0|))))))) :lblneg @23) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (<= 0 (_module.DList.freeStack |l'#0@0|)))))) (and (! (or %lbl%@24  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (< (_module.DList.freeStack |l'#0@0|) (|Seq#Length| (_module.DList.nodes |l'#0@0|)))))))) :lblneg @24) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (< (_module.DList.freeStack |l'#0@0|) (|Seq#Length| (_module.DList.nodes |l'#0@0|))))))) (and (! (or %lbl%@25  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|i#6| Int) ) (!  (=> true (and (=> (and (<= 0 |i#6|) (< |i#6| (|Seq#Length| (_module.DList.f |l'#0@0|)))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#6|))))) (=> (and (<= 0 |i#6|) (< |i#6| (|Seq#Length| (_module.DList.f |l'#0@0|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#6|))) (|Seq#Length| (_module.DList.nodes |l'#0@0|))))))
 :qid |DLLDafny.95:14|
 :skolemid |1454|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#6|)))
))))))) :lblneg @25) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|i#6@@0| Int) ) (!  (=> true (and (=> (and (<= 0 |i#6@@0|) (< |i#6@@0| (|Seq#Length| (_module.DList.f |l'#0@0|)))) (< 0 (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#6@@0|))))) (=> (and (<= 0 |i#6@@0|) (< |i#6@@0| (|Seq#Length| (_module.DList.f |l'#0@0|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#6@@0|))) (|Seq#Length| (_module.DList.nodes |l'#0@0|))))))
 :qid |DLLDafny.95:14|
 :skolemid |1454|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#6@@0|)))
)))))) (and (! (or %lbl%@26  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|i#7| Int) ) (!  (=> true (=> (and (<= 0 |i#7|) (< |i#7| (|Seq#Length| (_module.DList.f |l'#0@0|)))) (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#7|)))))) |i#7|)))
 :qid |DLLDafny.96:14|
 :skolemid |1455|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#7|))))))
))))))) :lblneg @26) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|i#7@@0| Int) ) (!  (=> true (=> (and (<= 0 |i#7@@0|) (< |i#7@@0| (|Seq#Length| (_module.DList.f |l'#0@0|)))) (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#7@@0|)))))) |i#7@@0|)))
 :qid |DLLDafny.96:14|
 :skolemid |1455|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) |i#7@@0|))))))
)))))) (and (! (or %lbl%@27  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#22| Int) ) (!  (=> true (and (=> (and (<= 0 |p#22|) (< |p#22| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#22|))))) (=> (and (<= 0 |p#22|) (< |p#22| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#22|))) (|Seq#Length| (_module.DList.s |l'#0@0|))))))
 :qid |DLLDafny.97:14|
 :skolemid |1456|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#22|)))
))))))) :lblneg @27) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#22@@0| Int) ) (!  (=> true (and (=> (and (<= 0 |p#22@@0|) (< |p#22@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 2) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#22@@0|))))) (=> (and (<= 0 |p#22@@0|) (< |p#22@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (< (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#22@@0|))) (|Seq#Length| (_module.DList.s |l'#0@0|))))))
 :qid |DLLDafny.97:14|
 :skolemid |1456|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#22@@0|)))
)))))) (and (! (or %lbl%@28  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#23| Int) ) (!  (=> true (and (=> (and (<= 0 |p#23|) (< |p#23| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#23|))))) (=> (and (<= 0 |p#23|) (< |p#23| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#23|))) (|Seq#Length| (_module.DList.g |l'#0@0|))))))
 :qid |DLLDafny.99:14|
 :skolemid |1457|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#23|)))
))))))) :lblneg @28) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#23@@0| Int) ) (!  (=> true (and (=> (and (<= 0 |p#23@@0|) (< |p#23@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= 0 (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#23@@0|))))) (=> (and (<= 0 |p#23@@0|) (< |p#23@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (< (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#23@@0|))) (|Seq#Length| (_module.DList.g |l'#0@0|))))))
 :qid |DLLDafny.99:14|
 :skolemid |1457|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#23@@0|)))
)))))) (and (! (or %lbl%@29  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#24| Int) ) (!  (=> true (=> (and (<= 0 |p#24|) (< |p#24| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#24|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#24|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#24|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#24|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1458|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#24|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#24|)))
))))))) :lblneg @29) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#24@@0| Int) ) (!  (=> true (=> (and (<= 0 |p#24@@0|) (< |p#24@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (and (=> (>= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#24@@0|))) 0) (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#24@@0|))))) (=> (_module.Option.Some_q (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#24@@0|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#24@@0|))) 0)))))
 :qid |DLLDafny.101:14|
 :skolemid |1458|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#24@@0|)))
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#24@@0|)))
)))))) (and (! (or %lbl%@30  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#25| Int) ) (!  (=> true (=> (and (and (<= 0 |p#25|) (< |p#25| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#25|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#25|))) (- 0 1)) (= |p#25| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1459|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#25|)))
))))))) :lblneg @30) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#25@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#25@@0|) (< |p#25@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#25@@0|))))) (=> (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#25@@0|))) (- 0 1)) (= |p#25@@0| 0))))
 :qid |DLLDafny.103:14|
 :skolemid |1459|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#25@@0|)))
)))))) (and (! (or %lbl%@31  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#26| Int) ) (!  (=> true (=> (and (and (<= 0 |p#26|) (< |p#26| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26|)))))) |p#26|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#26|))) (|#_module.Option.Some| (|Seq#Index| (_module.DList.s |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1460|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26|)))
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26|))))))
 :pattern ( (|Seq#Index| (_module.DList.s |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26|)))))
))))))) :lblneg @31) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#26@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#26@@0|) (< |p#26@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26@@0|))))) (=> (<= 0 (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26@@0|)))) (and (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26@@0|)))))) |p#26@@0|) (|_module.Option#Equal| (_module.Node.data ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#26@@0|))) (|#_module.Option.Some| (|Seq#Index| (_module.DList.s |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26@@0|))))))))))
 :qid |DLLDafny.105:14|
 :skolemid |1460|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26@@0|)))
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26@@0|))))))
 :pattern ( (|Seq#Index| (_module.DList.s |l'#0@0|) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#26@@0|)))))
)))))) (and (! (or %lbl%@32  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#27| Int) ) (!  (=> true (=> (and (and (<= 0 |p#27|) (< |p#27| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#27|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27|))) 1) (|Seq#Length| (_module.DList.f |l'#0@0|))) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1461|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#27|))))
))))))) :lblneg @32) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#27@@0| Int) ) (!  (=> true (=> (and (and (<= 0 |p#27@@0|) (< |p#27@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27@@0|))))) (= (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#27@@0|))) (ite (< (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27@@0|))) 1) (|Seq#Length| (_module.DList.f |l'#0@0|))) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (_module.__default.Add (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27@@0|))) 1)))) 0))))
 :qid |DLLDafny.108:14|
 :skolemid |1461|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#27@@0|)))
 :pattern ( (_module.Node.next ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#27@@0|))))
)))))) (and (! (or %lbl%@33  (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#28| Int) ) (!  (=> true (and (=> (and (and (<= 0 |p#28|) (< |p#28| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28|))))) true) (=> (and (and (<= 0 |p#28|) (< |p#28| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28|))))) (= (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#28|))) (ite (> (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28|))) 0) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28|))) 1)))) (ite  (or (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28|))) 0) (= (|Seq#Length| (_module.DList.f |l'#0@0|)) 0)) 0 (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (_module.__default.Sub (|Seq#Length| (_module.DList.f |l'#0@0|)) 1))))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1462|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#28|))))
))))))) :lblneg @33) (=> (=> (|_module.__default.Inv#canCall| _module._default.Remove$A |l'#0@0|) (or (_module.__default.Inv _module._default.Remove$A |l'#0@0|) (=> (|_module.__default.Invs#canCall| _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (or (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l'#0@0|) (_module.DList.freeStack |l'#0@0|) (_module.DList.s |l'#0@0|) (_module.DList.f |l'#0@0|) (_module.DList.g |l'#0@0|)) (forall ((|p#28@@0| Int) ) (!  (=> true (and (=> (and (and (<= 0 |p#28@@0|) (< |p#28@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28@@0|))))) true) (=> (and (and (<= 0 |p#28@@0|) (< |p#28@@0| (|Seq#Length| (_module.DList.g |l'#0@0|)))) (<= (- 0 1) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28@@0|))))) (= (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#28@@0|))) (ite (> (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28@@0|))) 0) (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (_module.__default.Sub (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28@@0|))) 1)))) (ite  (or (= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28@@0|))) 0) (= (|Seq#Length| (_module.DList.f |l'#0@0|)) 0)) 0 (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.f |l'#0@0|) (_module.__default.Sub (|Seq#Length| (_module.DList.f |l'#0@0|)) 1))))))))))
 :qid |DLLDafny.113:14|
 :skolemid |1462|
 :pattern ( ($Unbox intType (|Seq#Index| (_module.DList.g |l'#0@0|) |p#28@@0|)))
 :pattern ( (_module.Node.prev ($Unbox DatatypeTypeType (|Seq#Index| (_module.DList.nodes |l'#0@0|) |p#28@@0|))))
)))))) (and (! (or %lbl%@34 (|Seq#Equal| (_module.__default.Seq _module._default.Remove$A |l'#0@0|) (_module.__default.SeqRemove _module._default.Remove$A (_module.__default.Seq _module._default.Remove$A |l#0@@102|) (_module.__default.Index _module._default.Remove$A |l#0@@102| |p#0@@30|)))) :lblneg @34) (=> (|Seq#Equal| (_module.__default.Seq _module._default.Remove$A |l'#0@0|) (_module.__default.SeqRemove _module._default.Remove$A (_module.__default.Seq _module._default.Remove$A |l#0@@102|) (_module.__default.Index _module._default.Remove$A |l#0@@102| |p#0@@30|))) (! (or %lbl%@35 (forall ((|x#1@@1| Int) ) (!  (=> true (and (=> (and (not (= |x#1@@1| |p#0@@30|)) (_module.__default.ValidPtr _module._default.Remove$A |l#0@@102| |x#1@@1|)) (_module.__default.ValidPtr _module._default.Remove$A |l'#0@0| |x#1@@1|)) (=> (and (not (= |x#1@@1| |p#0@@30|)) (_module.__default.ValidPtr _module._default.Remove$A |l#0@@102| |x#1@@1|)) (ite (< (_module.__default.Index _module._default.Remove$A |l#0@@102| |x#1@@1|) (_module.__default.Index _module._default.Remove$A |l#0@@102| |p#0@@30|)) (= (_module.__default.Index _module._default.Remove$A |l'#0@0| |x#1@@1|) (_module.__default.Index _module._default.Remove$A |l#0@@102| |x#1@@1|)) (= (_module.__default.Index _module._default.Remove$A |l'#0@0| |x#1@@1|) (_module.__default.Sub (_module.__default.Index _module._default.Remove$A |l#0@@102| |x#1@@1|) 1))))))
 :qid |DLLDafny.292:18|
 :skolemid |1473|
 :pattern ( (_module.__default.Index _module._default.Remove$A |l'#0@0| |x#1@@1|))
 :pattern ( (_module.__default.ValidPtr _module._default.Remove$A |l#0@@102| |x#1@@1|))
 :pattern ( (_module.__default.ValidPtr _module._default.Remove$A |l'#0@0| |x#1@@1|))
))) :lblneg @35))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+36 true) :lblpos +36) (=> (and ($IsGoodHeap $Heap@@1) ($IsHeapAnchor $Heap@@1)) (=> (and (and (and (and (and ($Is |l#0@@102| (Tclass._module.DList _module._default.Remove$A)) ($IsAlloc |l#0@@102| (Tclass._module.DList _module._default.Remove$A) $Heap@@1)) (|$IsA#_module.DList| |l#0@@102|)) (and ($Is |l'#0| (Tclass._module.DList _module._default.Remove$A)) ($IsAlloc |l'#0| (Tclass._module.DList _module._default.Remove$A) $Heap@@1))) (and (and ($Is |s'#0| (TSeq _module._default.Remove$A)) ($IsAlloc |s'#0| (TSeq _module._default.Remove$A) $Heap@@1)) (and ($Is |f'#0| (TSeq TInt)) ($IsAlloc |f'#0| (TSeq TInt) $Heap@@1)))) (and (and (and (and ($Is |g'#0| (TSeq TInt)) ($IsAlloc |g'#0| (TSeq TInt) $Heap@@1)) (and ($Is |$rhs##0| (TSeq TInt)) ($IsAlloc |$rhs##0| (TSeq TInt) $Heap@@1))) (and (and ($Is |node#0| (Tclass._module.Node _module._default.Remove$A)) ($IsAlloc |node#0| (Tclass._module.Node _module._default.Remove$A) $Heap@@1)) (and ($Is |node_prev#0| (Tclass._module.Node _module._default.Remove$A)) ($IsAlloc |node_prev#0| (Tclass._module.Node _module._default.Remove$A) $Heap@@1)))) (and (and (and ($Is |node_next#0| (Tclass._module.Node _module._default.Remove$A)) ($IsAlloc |node_next#0| (Tclass._module.Node _module._default.Remove$A) $Heap@@1)) (= 37 $FunctionContextHeight)) (and (and (|_module.__default.Inv#canCall| _module._default.Remove$A |l#0@@102|) (and (and (and (and (and (_module.__default.Inv _module._default.Remove$A |l#0@@102|) ($Is (_module.DList.nodes |l#0@@102|) (TSeq (Tclass._module.Node _module._default.Remove$A)))) ($Is (_module.DList.s |l#0@@102|) (TSeq _module._default.Remove$A))) ($Is (_module.DList.f |l#0@@102|) (TSeq TInt))) ($Is (_module.DList.g |l#0@@102|) (TSeq TInt))) (_module.__default.Invs _module._default.Remove$A (_module.DList.nodes |l#0@@102|) (_module.DList.freeStack |l#0@@102|) (_module.DList.s |l#0@@102|) (_module.DList.f |l#0@@102|) (_module.DList.g |l#0@@102|)))) (and (|_module.__default.ValidPtr#canCall| _module._default.Remove$A |l#0@@102| |p#0@@30|) (and (_module.__default.ValidPtr _module._default.Remove$A |l#0@@102| |p#0@@30|) (and (and (< 0 |p#0@@30|) (< |p#0@@30| (|Seq#Length| (_module.DList.g |l#0@@102|)))) (>= (U_2_int ($Unbox intType (|Seq#Index| (_module.DList.g |l#0@@102|) |p#0@@30|))) 0)))))))) anon0_correct)))))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid
