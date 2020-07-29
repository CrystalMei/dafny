// Dafny 2.3.0.10506
// Command Line Options: /compile:0 /trace DLL_Dafny.dfy /proverOpt:LOGIC=DLA /print:DLL-Dafny2Boogie.bpl /proverLog:DLL-Dafny2z3.smt2

const $$Language$Dafny: bool;

axiom $$Language$Dafny;

type Ty;

type Bv0 = int;

const unique TBool: Ty;

const unique TChar: Ty;

const unique TInt: Ty;

const unique TReal: Ty;

const unique TORDINAL: Ty;

function TBitvector(int) : Ty;

function TSet(Ty) : Ty;

function TISet(Ty) : Ty;

function TMultiSet(Ty) : Ty;

function TSeq(Ty) : Ty;

function TMap(Ty, Ty) : Ty;

function TIMap(Ty, Ty) : Ty;

function Inv0_TBitvector(Ty) : int;

axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

function Inv0_TSet(Ty) : Ty;

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

function Inv0_TISet(Ty) : Ty;

axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);

function Inv0_TSeq(Ty) : Ty;

axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);

function Inv0_TMultiSet(Ty) : Ty;

axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);

function Inv0_TMap(Ty) : Ty;

function Inv1_TMap(Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv0_TMap(TMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv1_TMap(TMap(t, u)) == u);

function Inv0_TIMap(Ty) : Ty;

function Inv1_TIMap(Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv0_TIMap(TIMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv1_TIMap(TIMap(t, u)) == u);

type TyTag;

function Tag(Ty) : TyTag;

const unique TagBool: TyTag;

const unique TagChar: TyTag;

const unique TagInt: TyTag;

const unique TagReal: TyTag;

const unique TagORDINAL: TyTag;

const unique TagSet: TyTag;

const unique TagISet: TyTag;

const unique TagMultiSet: TyTag;

const unique TagSeq: TyTag;

const unique TagMap: TyTag;

const unique TagIMap: TyTag;

const unique TagClass: TyTag;

axiom Tag(TBool) == TagBool;

axiom Tag(TChar) == TagChar;

axiom Tag(TInt) == TagInt;

axiom Tag(TReal) == TagReal;

axiom Tag(TORDINAL) == TagORDINAL;

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

axiom (forall t: Ty :: { TISet(t) } Tag(TISet(t)) == TagISet);

axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Tag(TMap(t, u)) == TagMap);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Tag(TIMap(t, u)) == TagIMap);

function {:identity} Lit<T>(x: T) : T;

axiom (forall<T> x: T :: {:identity} { Lit(x): T } Lit(x): T == x);

axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)));

function {:inline} LitInt(x: int) : int
{
  x
}

axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)));

function {:identity} LitReal(x: real) : real;

axiom (forall x: real :: {:identity} { LitReal(x): real } LitReal(x): real == x);

axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)));

type char;

function char#FromInt(int) : char;

function char#ToInt(char) : int;

axiom (forall ch: char :: 
  { char#ToInt(ch) } 
  char#FromInt(char#ToInt(ch)) == ch
     && 0 <= char#ToInt(ch)
     && char#ToInt(ch) < 65536);

axiom (forall n: int :: 
  { char#FromInt(n) } 
  0 <= n && n < 65536 ==> char#ToInt(char#FromInt(n)) == n);

function char#Plus(char, char) : char;

function char#Minus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Plus(a, b) } 
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

axiom (forall a: char, b: char :: 
  { char#Minus(a, b) } 
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

type ref;

const null: ref;

type Box;

const $ArbitraryBoxValue: Box;

function $Box<T>(T) : Box;

function $Unbox<T>(Box) : T;

axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);

axiom (forall bx: Box :: 
  { $IsBox(bx, TInt) } 
  $IsBox(bx, TInt) ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, TInt));

axiom (forall bx: Box :: 
  { $IsBox(bx, TReal) } 
  $IsBox(bx, TReal)
     ==> $Box($Unbox(bx): real) == bx && $Is($Unbox(bx): real, TReal));

axiom (forall bx: Box :: 
  { $IsBox(bx, TBool) } 
  $IsBox(bx, TBool)
     ==> $Box($Unbox(bx): bool) == bx && $Is($Unbox(bx): bool, TBool));

axiom (forall bx: Box :: 
  { $IsBox(bx, TChar) } 
  $IsBox(bx, TChar)
     ==> $Box($Unbox(bx): char) == bx && $Is($Unbox(bx): char, TChar));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSet(t)) } 
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set Box) == bx && $Is($Unbox(bx): Set Box, TSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TISet(t)) } 
  $IsBox(bx, TISet(t))
     ==> $Box($Unbox(bx): ISet Box) == bx && $Is($Unbox(bx): ISet Box, TISet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TMultiSet(t)) } 
  $IsBox(bx, TMultiSet(t))
     ==> $Box($Unbox(bx): MultiSet Box) == bx
       && $Is($Unbox(bx): MultiSet Box, TMultiSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSeq(t)) } 
  $IsBox(bx, TSeq(t))
     ==> $Box($Unbox(bx): Seq Box) == bx && $Is($Unbox(bx): Seq Box, TSeq(t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TMap(s, t)) } 
  $IsBox(bx, TMap(s, t))
     ==> $Box($Unbox(bx): Map Box Box) == bx && $Is($Unbox(bx): Map Box Box, TMap(s, t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TIMap(s, t)) } 
  $IsBox(bx, TIMap(s, t))
     ==> $Box($Unbox(bx): IMap Box Box) == bx
       && $Is($Unbox(bx): IMap Box Box, TIMap(s, t)));

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

axiom (forall<T> v: T, t: Ty, h: Heap :: 
  { $IsAllocBox($Box(v), t, h) } 
  $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v, t, h));

function $Is<T>(T, Ty) : bool;

function $IsAlloc<T>(T, Ty, Heap) : bool;

function $IsBox<T>(T, Ty) : bool;

function $IsAllocBox<T>(T, Ty, Heap) : bool;

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal));

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall h: Heap, v: int :: { $IsAlloc(v, TInt, h) } $IsAlloc(v, TInt, h));

axiom (forall h: Heap, v: real :: { $IsAlloc(v, TReal, h) } $IsAlloc(v, TReal, h));

axiom (forall h: Heap, v: bool :: { $IsAlloc(v, TBool, h) } $IsAlloc(v, TBool, h));

axiom (forall h: Heap, v: char :: { $IsAlloc(v, TChar, h) } $IsAlloc(v, TChar, h));

axiom (forall h: Heap, v: ORDINAL :: 
  { $IsAlloc(v, TORDINAL, h) } 
  $IsAlloc(v, TORDINAL, h));

axiom (forall v: Set Box, t0: Ty :: 
  { $Is(v, TSet(t0)) } 
  $Is(v, TSet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: ISet Box, t0: Ty :: 
  { $Is(v, TISet(t0)) } 
  $Is(v, TISet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0))
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));

axiom (forall v: Seq Box, t0: Ty :: 
  { $Is(v, TSeq(t0)) } 
  $Is(v, TSeq(t0))
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Set Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSet(t0), h) } 
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: ISet Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TISet(t0), h) } 
  $IsAlloc(v, TISet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: MultiSet Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TMultiSet(t0), h) } 
  $IsAlloc(v, TMultiSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: Seq Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSeq(t0), h) } 
  $IsAlloc(v, TSeq(t0), h)
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsAllocBox(Seq#Index(v, i), t0, h)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] } 
      Map#Domain(v)[bx] ==> $IsBox(Map#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TMap(t0, t1), h) } 
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] } 
      Map#Domain(v)[bx]
         ==> $IsAllocBox(Map#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx] ==> $IsBox(IMap#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TIMap(t0, t1), h) } 
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx]
         ==> $IsAllocBox(IMap#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

type ClassName;

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

function Tclass._System.object?() : Ty;

function dtype(ref) : Ty;

function TypeTuple(a: ClassName, b: ClassName) : ClassName;

function TypeTupleCar(ClassName) : ClassName;

function TypeTupleCdr(ClassName) : ClassName;

axiom (forall a: ClassName, b: ClassName :: 
  { TypeTuple(a, b) } 
  TypeTupleCar(TypeTuple(a, b)) == a && TypeTupleCdr(TypeTuple(a, b)) == b);

type HandleType;

function SetRef_to_SetBox(s: [ref]bool) : Set Box;

axiom (forall s: [ref]bool, bx: Box :: 
  { SetRef_to_SetBox(s)[bx] } 
  SetRef_to_SetBox(s)[bx] == s[$Unbox(bx): ref]);

axiom (forall s: [ref]bool :: 
  { SetRef_to_SetBox(s) } 
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

type DatatypeType;

type DtCtorId;

function DatatypeCtorId(DatatypeType) : DtCtorId;

function DtRank(DatatypeType) : int;

function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

function ORD#IsNat(ORDINAL) : bool;

function ORD#Offset(ORDINAL) : int;

axiom (forall o: ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

function ORD#FromNat(int) : ORDINAL;

axiom (forall n: int :: 
  { ORD#FromNat(n) } 
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);

axiom (forall o: ORDINAL :: 
  { ORD#Offset(o) } { ORD#IsNat(o) } 
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

function ORD#Less(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p) } 
  (ORD#Less(o, p) ==> o != p)
     && (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o, p))
     && (ORD#IsNat(o) && ORD#IsNat(p)
       ==> ORD#Less(o, p) == (ORD#Offset(o) < ORD#Offset(p)))
     && (ORD#Less(o, p) && ORD#IsNat(p) ==> ORD#IsNat(o)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, o) } 
  ORD#Less(o, p) || o == p || ORD#Less(p, o));

axiom (forall o: ORDINAL, p: ORDINAL, r: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, r) } { ORD#Less(o, p), ORD#Less(o, r) } 
  ORD#Less(o, p) && ORD#Less(p, r) ==> ORD#Less(o, r));

function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#LessThanLimit(o, p) } 
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (ORD#IsNat(ORD#Plus(o, p)) ==> ORD#IsNat(o) && ORD#IsNat(p))
     && (ORD#IsNat(p)
       ==> ORD#IsNat(ORD#Plus(o, p)) == ORD#IsNat(o)
         && ORD#Offset(ORD#Plus(o, p)) == ORD#Offset(o) + ORD#Offset(p)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p)))
     && (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p)
     && (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));

function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> ORD#IsNat(ORD#Minus(o, p)) == ORD#IsNat(o)
       && ORD#Offset(ORD#Minus(o, p)) == ORD#Offset(o) - ORD#Offset(p));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> (p == ORD#FromNat(0) && ORD#Minus(o, p) == o)
       || (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n
     ==> ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Plus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && m + n <= ORD#Offset(o)
     ==> ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Minus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(n - m))));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(n - m))));

const $ModuleContextHeight: int;

const $FunctionContextHeight: int;

type LayerType;

const $LZ: LayerType;

function $LS(LayerType) : LayerType;

function AsFuelBottom(LayerType) : LayerType;

function AtLayer<A>([LayerType]A, LayerType) : A;

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, ly) } 
  AtLayer(f, ly) == f[ly]);

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, $LS(ly)) } 
  AtLayer(f, $LS(ly)) == AtLayer(f, ly));

type Field _;

function FDim<T>(Field T) : int;

function IndexField(int) : Field Box;

axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);

function IndexField_Inverse<T>(Field T) : int;

axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function MultiIndexField(Field Box, int) : Field Box;

axiom (forall f: Field Box, i: int :: 
  { MultiIndexField(f, i) } 
  FDim(MultiIndexField(f, i)) == FDim(f) + 1);

function MultiIndexField_Inverse0<T>(Field T) : Field T;

function MultiIndexField_Inverse1<T>(Field T) : int;

axiom (forall f: Field Box, i: int :: 
  { MultiIndexField(f, i) } 
  MultiIndexField_Inverse0(MultiIndexField(f, i)) == f
     && MultiIndexField_Inverse1(MultiIndexField(f, i)) == i);

function DeclType<T>(Field T) : ClassName;

type NameFamily;

function DeclName<T>(Field T) : NameFamily;

function FieldOfDecl<alpha>(ClassName, NameFamily) : Field alpha;

axiom (forall<T> cl: ClassName, nm: NameFamily :: 
  { FieldOfDecl(cl, nm): Field T } 
  DeclType(FieldOfDecl(cl, nm): Field T) == cl
     && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

function $IsGhostField<T>(Field T) : bool;

axiom (forall<T> h: Heap, k: Heap, v: T, t: Ty :: 
  { $HeapSucc(h, k), $IsAlloc(v, t, h) } 
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));

axiom (forall h: Heap, k: Heap, bx: Box, t: Ty :: 
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) } 
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

const unique alloc: Field bool;

const unique allocName: NameFamily;

axiom FDim(alloc) == 0 && DeclName(alloc) == allocName && !$IsGhostField(alloc);

function _System.array.Length(a: ref) : int;

axiom (forall o: ref :: 0 <= _System.array.Length(o));

function Int(x: real) : int;

axiom (forall x: real :: { Int(x): int } Int(x): int == int(x));

function Real(x: int) : real;

axiom (forall x: int :: { Real(x): real } Real(x): real == real(x));

axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

function {:inline} _System.real.Floor(x: real) : int
{
  Int(x)
}

type Heap = [ref]<alpha>[Field alpha]alpha;

function {:inline} read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha
{
  H[r][f]
}

function {:inline} update<alpha>(H: Heap, r: ref, f: Field alpha, v: alpha) : Heap
{
  H[r := H[r][f := v]]
}

function $IsGoodHeap(Heap) : bool;

function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap;

axiom $IsGoodHeap($OneHeap);

function $HeapSucc(Heap, Heap) : bool;

axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: 
  { update(h, r, f, x) } 
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap :: 
  { $HeapSucc(a, b), $HeapSucc(b, c) } 
  a != c ==> $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap :: 
  { $HeapSucc(h, k) } 
  $HeapSucc(h, k)
     ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

function $HeapSuccGhost(Heap, Heap) : bool;

axiom (forall h: Heap, k: Heap :: 
  { $HeapSuccGhost(h, k) } 
  $HeapSuccGhost(h, k)
     ==> $HeapSucc(h, k)
       && (forall<alpha> o: ref, f: Field alpha :: 
        { read(k, o, f) } 
        !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

type TickType;

var $Tick: TickType;

procedure $YieldHavoc(this: ref, rds: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> 
      $o == this || rds[$Box($o)] || nw[$Box($o)]
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc0(this: ref, rds: Set Box, modi: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> 
      rds[$Box($o)] && !modi[$Box($o)] && $o != this
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc1(this: ref, modi: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || $o == this
         || modi[$Box($o)]
         || nw[$Box($o)]);
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set Box))
   returns (s: Set Box);
  ensures (forall bx: Box :: 
    { s[bx] } 
    s[bx]
       <==> read(newHeap, this, NW)[bx]
         || (
          $Unbox(bx) != null
           && !read(prevHeap, $Unbox(bx): ref, alloc)
           && read(newHeap, $Unbox(bx): ref, alloc)));



type Set T = [T]bool;

function Set#Card<T>(Set T) : int;

axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>() : Set T;

axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

axiom (forall<T> s: Set T :: 
  { Set#Card(s) } 
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

function Set#Singleton<T>(T) : Set T;

axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);

axiom (forall<T> r: T, o: T :: 
  { Set#Singleton(r)[o] } 
  Set#Singleton(r)[o] <==> r == o);

axiom (forall<T> r: T :: 
  { Set#Card(Set#Singleton(r)) } 
  Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T) : Set T;

axiom (forall<T> a: Set T, x: T, o: T :: 
  { Set#UnionOne(a, x)[o] } 
  Set#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) } Set#UnionOne(a, x)[x]);

axiom (forall<T> a: Set T, x: T, y: T :: 
  { Set#UnionOne(a, x), a[y] } 
  a[y] ==> Set#UnionOne(a, x)[y]);

axiom (forall<T> a: Set T, x: T :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

axiom (forall<T> a: Set T, x: T :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T :: 
  { Set#Union(a, b)[o] } 
  Set#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { Set#Union(a, b), a[y] } 
  a[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { Set#Union(a, b), b[y] } 
  b[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Union(a, b) } 
  Set#Disjoint(a, b)
     ==> Set#Difference(Set#Union(a, b), a) == b
       && Set#Difference(Set#Union(a, b), b) == a);

function Set#Intersection<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T :: 
  { Set#Intersection(a, b)[o] } 
  Set#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Union(Set#Union(a, b), b) } 
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Union(a, Set#Union(a, b)) } 
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Intersection(Set#Intersection(a, b), b) } 
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Intersection(a, Set#Intersection(a, b)) } 
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) } 
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T :: 
  { Set#Difference(a, b)[o] } 
  Set#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { Set#Difference(a, b), b[y] } 
  b[y] ==> !Set#Difference(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Card(Set#Difference(a, b)) } 
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Subset(a, b) } 
  Set#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function Set#Equal<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Equal(a, b) } 
  Set#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: Set T, b: Set T :: { Set#Equal(a, b) } Set#Equal(a, b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Disjoint(a, b) } 
  Set#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

type ISet T = [T]bool;

function ISet#Empty<T>() : Set T;

axiom (forall<T> o: T :: { ISet#Empty()[o] } !ISet#Empty()[o]);

function ISet#UnionOne<T>(ISet T, T) : ISet T;

axiom (forall<T> a: ISet T, x: T, o: T :: 
  { ISet#UnionOne(a, x)[o] } 
  ISet#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: ISet T, x: T :: { ISet#UnionOne(a, x) } ISet#UnionOne(a, x)[x]);

axiom (forall<T> a: ISet T, x: T, y: T :: 
  { ISet#UnionOne(a, x), a[y] } 
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T :: 
  { ISet#Union(a, b)[o] } 
  ISet#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T :: 
  { ISet#Union(a, b), a[y] } 
  a[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { ISet#Union(a, b), b[y] } 
  b[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Union(a, b) } 
  ISet#Disjoint(a, b)
     ==> ISet#Difference(ISet#Union(a, b), a) == b
       && ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T :: 
  { ISet#Intersection(a, b)[o] } 
  ISet#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Union(ISet#Union(a, b), b) } 
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { ISet#Union(a, ISet#Union(a, b)) } 
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Intersection(ISet#Intersection(a, b), b) } 
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Intersection(a, ISet#Intersection(a, b)) } 
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));

function ISet#Difference<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T :: 
  { ISet#Difference(a, b)[o] } 
  ISet#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T :: 
  { ISet#Difference(a, b), b[y] } 
  b[y] ==> !ISet#Difference(a, b)[y]);

function ISet#Subset<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Subset(a, b) } 
  ISet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function ISet#Equal<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Equal(a, b) } 
  ISet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Equal(a, b) } 
  ISet#Equal(a, b) ==> a == b);

function ISet#Disjoint<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Disjoint(a, b) } 
  ISet#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

function Math#min(a: int, b: int) : int;

axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);

axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);

axiom (forall a: int, b: int :: 
  { Math#min(a, b) } 
  Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int) : int;

axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);

axiom (forall a: int :: { Math#clip(a) } a < 0 ==> Math#clip(a) == 0);

type MultiSet T = [T]int;

function $IsGoodMultiSet<T>(ms: MultiSet T) : bool;

axiom (forall<T> ms: MultiSet T :: 
  { $IsGoodMultiSet(ms) } 
  $IsGoodMultiSet(ms)
     <==> (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

function MultiSet#Card<T>(MultiSet T) : int;

axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));

axiom (forall<T> s: MultiSet T, x: T, n: int :: 
  { MultiSet#Card(s[x := n]) } 
  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

function MultiSet#Empty<T>() : MultiSet T;

axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);

axiom (forall<T> s: MultiSet T :: 
  { MultiSet#Card(s) } 
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty())
     && (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));

function MultiSet#Singleton<T>(T) : MultiSet T;

axiom (forall<T> r: T, o: T :: 
  { MultiSet#Singleton(r)[o] } 
  (MultiSet#Singleton(r)[o] == 1 <==> r == o)
     && (MultiSet#Singleton(r)[o] == 0 <==> r != o));

axiom (forall<T> r: T :: 
  { MultiSet#Singleton(r) } 
  MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

function MultiSet#UnionOne<T>(MultiSet T, T) : MultiSet T;

axiom (forall<T> a: MultiSet T, x: T, o: T :: 
  { MultiSet#UnionOne(a, x)[o] } 
  0 < MultiSet#UnionOne(a, x)[o] <==> o == x || 0 < a[o]);

axiom (forall<T> a: MultiSet T, x: T :: 
  { MultiSet#UnionOne(a, x) } 
  MultiSet#UnionOne(a, x)[x] == a[x] + 1);

axiom (forall<T> a: MultiSet T, x: T, y: T :: 
  { MultiSet#UnionOne(a, x), a[y] } 
  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T, y: T :: 
  { MultiSet#UnionOne(a, x), a[y] } 
  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T :: 
  { MultiSet#Card(MultiSet#UnionOne(a, x)) } 
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);

function MultiSet#Union<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: 
  { MultiSet#Union(a, b)[o] } 
  MultiSet#Union(a, b)[o] == a[o] + b[o]);

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Card(MultiSet#Union(a, b)) } 
  MultiSet#Card(MultiSet#Union(a, b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: 
  { MultiSet#Intersection(a, b)[o] } 
  MultiSet#Intersection(a, b)[o] == Math#min(a[o], b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Intersection(MultiSet#Intersection(a, b), b) } 
  MultiSet#Intersection(MultiSet#Intersection(a, b), b)
     == MultiSet#Intersection(a, b));

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) } 
  MultiSet#Intersection(a, MultiSet#Intersection(a, b))
     == MultiSet#Intersection(a, b));

function MultiSet#Difference<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: 
  { MultiSet#Difference(a, b)[o] } 
  MultiSet#Difference(a, b)[o] == Math#clip(a[o] - b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T, y: T :: 
  { MultiSet#Difference(a, b), b[y], a[y] } 
  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0);

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Card(MultiSet#Difference(a, b)) } 
  MultiSet#Card(MultiSet#Difference(a, b))
         + MultiSet#Card(MultiSet#Difference(b, a))
         + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
       == MultiSet#Card(MultiSet#Union(a, b))
     && MultiSet#Card(MultiSet#Difference(a, b))
       == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

function MultiSet#Subset<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Subset(a, b) } 
  MultiSet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <= b[o]));

function MultiSet#Equal<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] == b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Disjoint(a, b) } 
  MultiSet#Disjoint(a, b)
     <==> (forall o: T :: { a[o] } { b[o] } a[o] == 0 || b[o] == 0));

function MultiSet#FromSet<T>(Set T) : MultiSet T;

axiom (forall<T> s: Set T, a: T :: 
  { MultiSet#FromSet(s)[a] } 
  (MultiSet#FromSet(s)[a] == 0 <==> !s[a])
     && (MultiSet#FromSet(s)[a] == 1 <==> s[a]));

axiom (forall<T> s: Set T :: 
  { MultiSet#Card(MultiSet#FromSet(s)) } 
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

function MultiSet#FromSeq<T>(Seq T) : MultiSet T;

axiom (forall<T> s: Seq T :: 
  { MultiSet#FromSeq(s) } 
  $IsGoodMultiSet(MultiSet#FromSeq(s)));

axiom (forall<T> s: Seq T :: 
  { MultiSet#Card(MultiSet#FromSeq(s)) } 
  MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));

axiom (forall<T> s: Seq T, v: T :: 
  { MultiSet#FromSeq(Seq#Build(s, v)) } 
  MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));

axiom (forall<T>  :: 
  MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);

axiom (forall<T> a: Seq T, b: Seq T :: 
  { MultiSet#FromSeq(Seq#Append(a, b)) } 
  MultiSet#FromSeq(Seq#Append(a, b))
     == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));

axiom (forall<T> s: Seq T, i: int, v: T, x: T :: 
  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] } 
  0 <= i && i < Seq#Length(s)
     ==> MultiSet#FromSeq(Seq#Update(s, i, v))[x]
       == MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))), 
        MultiSet#Singleton(v))[x]);

axiom (forall<T> s: Seq T, x: T :: 
  { MultiSet#FromSeq(s)[x] } 
  (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i))
     <==> 0 < MultiSet#FromSeq(s)[x]);

type Seq _;

function Seq#Length<T>(Seq T) : int;

axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>() : Seq T;

axiom (forall<T>  :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);

axiom (forall<T> s: Seq T :: 
  { Seq#Length(s) } 
  Seq#Length(s) == 0 ==> s == Seq#Empty());

axiom (forall<T> t: Ty :: { $Is(Seq#Empty(): Seq T, t) } $Is(Seq#Empty(): Seq T, t));

function Seq#Singleton<T>(T) : Seq T;

axiom (forall<T> t: T :: 
  { Seq#Length(Seq#Singleton(t)) } 
  Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T) : Seq T;

function Seq#Build_inv0<T>(s: Seq T) : Seq T;

function Seq#Build_inv1<T>(s: Seq T) : T;

axiom (forall<T> s: Seq T, val: T :: 
  { Seq#Build(s, val) } 
  Seq#Build_inv0(Seq#Build(s, val)) == s
     && Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall<T> s: Seq T, v: T :: 
  { Seq#Build(s, v) } 
  Seq#Length(Seq#Build(s, v)) == 1 + Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T :: 
  { Seq#Index(Seq#Build(s, v), i) } 
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == v)
     && (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == Seq#Index(s, i)));

axiom (forall s: Seq Box, bx: Box, t: Ty :: 
  { $Is(Seq#Build(s, bx), TSeq(t)) } 
  $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType) : Seq Box;

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType :: 
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) } 
  $IsGoodHeap(heap) && 0 <= len
     ==> Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) == len);

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int :: 
  { Seq#Index(Seq#Create(ty, heap, len, init), i) } 
  $IsGoodHeap(heap) && 0 <= i && i < len
     ==> Seq#Index(Seq#Create(ty, heap, len, init), i)
       == Apply1(TInt, TSeq(ty), heap, init, $Box(i)));

function Seq#Append<T>(Seq T, Seq T) : Seq T;

axiom (forall<T> s0: Seq T, s1: Seq T :: 
  { Seq#Length(Seq#Append(s0, s1)) } 
  Seq#Length(Seq#Append(s0, s1)) == Seq#Length(s0) + Seq#Length(s1));

axiom (forall s0: Seq Box, s1: Seq Box, t: Ty :: 
  { $Is(Seq#Append(s0, s1), t) } 
  $Is(s0, t) && $Is(s1, t) ==> $Is(Seq#Append(s0, s1), t));

function Seq#Index<T>(Seq T, int) : T;

axiom (forall<T> t: T :: 
  { Seq#Index(Seq#Singleton(t), 0) } 
  Seq#Index(Seq#Singleton(t), 0) == t);

axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: 
  { Seq#Index(Seq#Append(s0, s1), n) } 
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update<T>(Seq T, int, T) : Seq T;

axiom (forall<T> s: Seq T, i: int, v: T :: 
  { Seq#Length(Seq#Update(s, i, v)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s, i, v)) == Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Index(Seq#Update(s, i, v), n) } 
  0 <= n && n < Seq#Length(s)
     ==> (i == n ==> Seq#Index(Seq#Update(s, i, v), n) == v)
       && (i != n ==> Seq#Index(Seq#Update(s, i, v), n) == Seq#Index(s, n)));

function Seq#Contains<T>(Seq T, T) : bool;

axiom (forall<T> s: Seq T, x: T :: 
  { Seq#Contains(s, x) } 
  Seq#Contains(s, x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> x: T :: 
  { Seq#Contains(Seq#Empty(), x) } 
  !Seq#Contains(Seq#Empty(), x));

axiom (forall<T> s0: Seq T, s1: Seq T, x: T :: 
  { Seq#Contains(Seq#Append(s0, s1), x) } 
  Seq#Contains(Seq#Append(s0, s1), x)
     <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T :: 
  { Seq#Contains(Seq#Build(s, v), x) } 
  Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));

axiom (forall<T> s: Seq T, n: int, x: T :: 
  { Seq#Contains(Seq#Take(s, n), x) } 
  Seq#Contains(Seq#Take(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> s: Seq T, n: int, x: T :: 
  { Seq#Contains(Seq#Drop(s, n), x) } 
  Seq#Contains(Seq#Drop(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T :: 
  { Seq#Equal(s0, s1) } 
  Seq#Equal(s0, s1)
     <==> Seq#Length(s0) == Seq#Length(s1)
       && (forall j: int :: 
        { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a, b) } Seq#Equal(a, b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: 
  { Seq#SameUntil(s0, s1, n) } 
  Seq#SameUntil(s0, s1, n)
     <==> (forall j: int :: 
      { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
      0 <= j && j < n ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

function Seq#Take<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Length(Seq#Take(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s, n)) == n);

axiom (forall<T> s: Seq T, n: int, j: int :: 
  {:weight 25} { Seq#Index(Seq#Take(s, n), j) } { Seq#Index(s, j), Seq#Take(s, n) } 
  0 <= j && j < n && j < Seq#Length(s)
     ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Length(Seq#Drop(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s, n)) == Seq#Length(s) - n);

axiom (forall<T> s: Seq T, n: int, j: int :: 
  {:weight 25} { Seq#Index(Seq#Drop(s, n), j) } 
  0 <= n && 0 <= j && j < Seq#Length(s) - n
     ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j + n));

axiom (forall<T> s: Seq T, n: int, k: int :: 
  {:weight 25} { Seq#Index(s, k), Seq#Drop(s, n) } 
  0 <= n && n <= k && k < Seq#Length(s)
     ==> Seq#Index(Seq#Drop(s, n), k - n) == Seq#Index(s, k));

axiom (forall<T> s: Seq T, t: Seq T, n: int :: 
  { Seq#Take(Seq#Append(s, t), n) } { Seq#Drop(Seq#Append(s, t), n) } 
  n == Seq#Length(s)
     ==> Seq#Take(Seq#Append(s, t), n) == s && Seq#Drop(Seq#Append(s, t), n) == t);

function Seq#FromArray(h: Heap, a: ref) : Seq Box;

axiom (forall h: Heap, a: ref :: 
  { Seq#Length(Seq#FromArray(h, a)) } 
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));

axiom (forall h: Heap, a: ref :: 
  { Seq#FromArray(h, a) } 
  (forall i: int :: 
    { read(h, a, IndexField(i)) } { Seq#Index(Seq#FromArray(h, a): Seq Box, i) } 
    0 <= i && i < Seq#Length(Seq#FromArray(h, a))
       ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));

axiom (forall h0: Heap, h1: Heap, a: ref :: 
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) } 
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) && h0[a] == h1[a]
     ==> Seq#FromArray(h0, a) == Seq#FromArray(h1, a));

axiom (forall h: Heap, i: int, v: Box, a: ref :: 
  { Seq#FromArray(update(h, a, IndexField(i), v), a) } 
  0 <= i && i < _System.array.Length(a)
     ==> Seq#FromArray(update(h, a, IndexField(i), v), a)
       == Seq#Update(Seq#FromArray(h, a), i, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  n <= i && i < Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= n && n <= i && i < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i - n, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

axiom (forall h: Heap, a: ref, n0: int, n1: int :: 
  { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) } 
  n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a)
     ==> Seq#Take(Seq#FromArray(h, a), n1)
       == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)));

axiom (forall<T> s: Seq T, v: T, n: int :: 
  { Seq#Drop(Seq#Build(s, v), n) } 
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v));

function Seq#Rank<T>(Seq T) : int;

axiom (forall s: Seq Box, i: int :: 
  { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) } 
  0 <= i && i < Seq#Length(s)
     ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int :: 
  { Seq#Rank(Seq#Drop(s, i)) } 
  0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int :: 
  { Seq#Rank(Seq#Take(s, i)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int, j: int :: 
  { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) } 
  0 <= i && i < j && j <= Seq#Length(s)
     ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s));

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Drop(s, n) } 
  n == 0 ==> Seq#Drop(s, n) == s);

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Take(s, n) } 
  n == 0 ==> Seq#Take(s, n) == Seq#Empty());

axiom (forall<T> s: Seq T, m: int, n: int :: 
  { Seq#Drop(Seq#Drop(s, m), n) } 
  0 <= m && 0 <= n && m + n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m + n));

type Map _ _;

function Map#Domain<U,V>(Map U V) : Set U;

function Map#Elements<U,V>(Map U V) : [U]V;

function Map#Card<U,V>(Map U V) : int;

axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall<U,V> m: Map U V :: 
  { Set#Card(Map#Domain(m)) } 
  Set#Card(Map#Domain(m)) == Map#Card(m));

function Map#Values<U,V>(Map U V) : Set V;

axiom (forall<U,V> m: Map U V, v: V :: 
  { Map#Values(m)[v] } 
  Map#Values(m)[v]
     == (exists u: U :: 
      { Map#Domain(m)[u] } { Map#Elements(m)[u] } 
      Map#Domain(m)[u] && v == Map#Elements(m)[u]));

function Map#Items<U,V>(Map U V) : Set Box;

function _System.Tuple2._0(DatatypeType) : Box;

function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall<U,V> m: Map U V :: 
  { Set#Card(Map#Items(m)) } 
  Set#Card(Map#Items(m)) == Map#Card(m));

axiom (forall m: Map Box Box, item: Box :: 
  { Map#Items(m)[item] } 
  Map#Items(m)[item]
     <==> Map#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && Map#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

function Map#Empty<U,V>() : Map U V;

axiom (forall<U,V> u: U :: 
  { Map#Domain(Map#Empty(): Map U V)[u] } 
  !Map#Domain(Map#Empty(): Map U V)[u]);

axiom (forall<U,V> m: Map U V :: 
  { Map#Card(m) } 
  (Map#Card(m) == 0 <==> m == Map#Empty())
     && (Map#Card(m) != 0 ==> (exists x: U :: Map#Domain(m)[x])));

function Map#Glue<U,V>([U]bool, [U]V, Ty) : Map U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { Map#Domain(Map#Glue(a, b, t)) } 
  Map#Domain(Map#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { Map#Elements(Map#Glue(a, b, t)) } 
  Map#Elements(Map#Glue(a, b, t)) == b);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { $Is(Map#Glue(a, b, t), t) } 
  $Is(Map#Glue(a, b, t), t));

function Map#Build<U,V>(Map U V, U, V) : Map U V;

axiom (forall<U,V> m: Map U V, u: U, u': U, v: V :: 
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] } 
  (u' == u
       ==> Map#Domain(Map#Build(m, u, v))[u'] && Map#Elements(Map#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u']
         && Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

axiom (forall<U,V> m: Map U V, u: U, v: V :: 
  { Map#Card(Map#Build(m, u, v)) } 
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

axiom (forall<U,V> m: Map U V, u: U, v: V :: 
  { Map#Card(Map#Build(m, u, v)) } 
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

function Map#Equal<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V :: 
  { Map#Equal(m, m') } 
  Map#Equal(m, m')
     <==> (forall u: U :: Map#Domain(m)[u] == Map#Domain(m')[u])
       && (forall u: U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

axiom (forall<U,V> m: Map U V, m': Map U V :: 
  { Map#Equal(m, m') } 
  Map#Equal(m, m') ==> m == m');

function Map#Disjoint<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V :: 
  { Map#Disjoint(m, m') } 
  Map#Disjoint(m, m')
     <==> (forall o: U :: 
      { Map#Domain(m)[o] } { Map#Domain(m')[o] } 
      !Map#Domain(m)[o] || !Map#Domain(m')[o]));

type IMap _ _;

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Elements<U,V>(IMap U V) : [U]V;

function IMap#Values<U,V>(IMap U V) : Set V;

axiom (forall<U,V> m: IMap U V, v: V :: 
  { IMap#Values(m)[v] } 
  IMap#Values(m)[v]
     == (exists u: U :: 
      { IMap#Domain(m)[u] } { IMap#Elements(m)[u] } 
      IMap#Domain(m)[u] && v == IMap#Elements(m)[u]));

function IMap#Items<U,V>(IMap U V) : Set Box;

axiom (forall m: IMap Box Box, item: Box :: 
  { IMap#Items(m)[item] } 
  IMap#Items(m)[item]
     <==> IMap#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && IMap#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

function IMap#Empty<U,V>() : IMap U V;

axiom (forall<U,V> u: U :: 
  { IMap#Domain(IMap#Empty(): IMap U V)[u] } 
  !IMap#Domain(IMap#Empty(): IMap U V)[u]);

function IMap#Glue<U,V>([U]bool, [U]V, Ty) : IMap U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { IMap#Domain(IMap#Glue(a, b, t)) } 
  IMap#Domain(IMap#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { IMap#Elements(IMap#Glue(a, b, t)) } 
  IMap#Elements(IMap#Glue(a, b, t)) == b);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { $Is(IMap#Glue(a, b, t), t) } 
  $Is(IMap#Glue(a, b, t), t));

function IMap#Build<U,V>(IMap U V, U, V) : IMap U V;

axiom (forall<U,V> m: IMap U V, u: U, u': U, v: V :: 
  { IMap#Domain(IMap#Build(m, u, v))[u'] } 
    { IMap#Elements(IMap#Build(m, u, v))[u'] } 
  (u' == u
       ==> IMap#Domain(IMap#Build(m, u, v))[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

function IMap#Equal<U,V>(IMap U V, IMap U V) : bool;

axiom (forall<U,V> m: IMap U V, m': IMap U V :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m')
     <==> (forall u: U :: IMap#Domain(m)[u] == IMap#Domain(m')[u])
       && (forall u: U :: 
        IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));

axiom (forall<U,V> m: IMap U V, m': IMap U V :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m') ==> m == m');

function INTERNAL_add_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_add_boogie(x, y): int } 
  INTERNAL_add_boogie(x, y): int == x + y);

function INTERNAL_sub_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_sub_boogie(x, y): int } 
  INTERNAL_sub_boogie(x, y): int == x - y);

function INTERNAL_mul_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_mul_boogie(x, y): int } 
  INTERNAL_mul_boogie(x, y): int == x * y);

function INTERNAL_div_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_div_boogie(x, y): int } 
  INTERNAL_div_boogie(x, y): int == x div y);

function INTERNAL_mod_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_mod_boogie(x, y): int } 
  INTERNAL_mod_boogie(x, y): int == x mod y);

function {:never_pattern true} INTERNAL_lt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_lt_boogie(x, y): bool } 
  INTERNAL_lt_boogie(x, y): bool == (x < y));

function {:never_pattern true} INTERNAL_le_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_le_boogie(x, y): bool } 
  INTERNAL_le_boogie(x, y): bool == (x <= y));

function {:never_pattern true} INTERNAL_gt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_gt_boogie(x, y): bool } 
  INTERNAL_gt_boogie(x, y): bool == (x > y));

function {:never_pattern true} INTERNAL_ge_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_ge_boogie(x, y): bool } 
  INTERNAL_ge_boogie(x, y): bool == (x >= y));

function {:inline} Mul(x: int, y: int) : int
{
  x * y
}

function {:inline} Div(x: int, y: int) : int
{
  x div y
}

function {:inline} Mod(x: int, y: int) : int
{
  x mod y
}

function {:inline} Add(x: int, y: int) : int
{
  x + y
}

function {:inline} Sub(x: int, y: int) : int
{
  x - y
}

function Tclass._System.nat() : Ty;

// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat;

const unique Tagclass._System.nat: TyTag;

// Box/unbox axiom for Tclass._System.nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.nat()) } 
  $IsBox(bx, Tclass._System.nat())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._System.nat()));

// _System.nat: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._System.nat()) } 
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

// _System.nat: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._System.nat(), $h) } 
  $IsAlloc(x#0, Tclass._System.nat(), $h));

const unique class._System.object?: ClassName;

// Tclass._System.object? Tag
axiom Tag(Tclass._System.object?()) == Tagclass._System.object?;

const unique Tagclass._System.object?: TyTag;

// Box/unbox axiom for Tclass._System.object?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object?()) } 
  $IsBox(bx, Tclass._System.object?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object?()));

// object: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._System.object?()) } 
  $Is($o, Tclass._System.object?()));

// object: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.object?(), $h) } 
  $IsAlloc($o, Tclass._System.object?(), $h)
     <==> $o == null || read($h, $o, alloc));

function implements$_System.object(Ty) : bool;

function Tclass._System.object() : Ty;

// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object;

const unique Tagclass._System.object: TyTag;

// Box/unbox axiom for Tclass._System.object
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object()) } 
  $IsBox(bx, Tclass._System.object())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object()));

// _System.object: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._System.object()) } 
  $Is(c#0, Tclass._System.object())
     <==> $Is(c#0, Tclass._System.object?()) && c#0 != null);

// _System.object: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.object(), $h) } 
  $IsAlloc(c#0, Tclass._System.object(), $h)
     <==> $IsAlloc(c#0, Tclass._System.object?(), $h));

const unique class._System.array?: ClassName;

function Tclass._System.array?(Ty) : Ty;

// Tclass._System.array? Tag
axiom (forall #$arg: Ty :: 
  { Tclass._System.array?(#$arg) } 
  Tag(Tclass._System.array?(#$arg)) == Tagclass._System.array?);

const unique Tagclass._System.array?: TyTag;

// Tclass._System.array? injectivity 0
axiom (forall #$arg: Ty :: 
  { Tclass._System.array?(#$arg) } 
  Tclass._System.array?_0(Tclass._System.array?(#$arg)) == #$arg);

function Tclass._System.array?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array?
axiom (forall #$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array?(#$arg)) } 
  $IsBox(bx, Tclass._System.array?(#$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array?(#$arg)));

// array.: Type axiom
axiom (forall #$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(#$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(#$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
     ==> $IsBox(read($h, $o, IndexField($i0)), #$arg));

// array.: Allocation axiom
axiom (forall #$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(#$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(#$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, IndexField($i0)), #$arg, $h));

// array: Class $Is
axiom (forall #$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array?(#$arg)) } 
  $Is($o, Tclass._System.array?(#$arg))
     <==> $o == null || dtype($o) == Tclass._System.array?(#$arg));

// array: Class $IsAlloc
axiom (forall #$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array?(#$arg), $h) } 
  $IsAlloc($o, Tclass._System.array?(#$arg), $h)
     <==> $o == null || read($h, $o, alloc));

// array.Length: Type axiom
axiom (forall #$arg: Ty, $o: ref :: 
  { _System.array.Length($o), Tclass._System.array?(#$arg) } 
  $o != null && dtype($o) == Tclass._System.array?(#$arg)
     ==> $Is(_System.array.Length($o), TInt));

// array.Length: Allocation axiom
axiom (forall #$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array.Length($o), read($h, $o, alloc), Tclass._System.array?(#$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(#$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array.Length($o), TInt, $h));

function Tclass._System.array(Ty) : Ty;

// Tclass._System.array Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tag(Tclass._System.array(_System.array$arg)) == Tagclass._System.array);

const unique Tagclass._System.array: TyTag;

// Tclass._System.array injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tclass._System.array_0(Tclass._System.array(_System.array$arg))
     == _System.array$arg);

function Tclass._System.array_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array(_System.array$arg)));

// _System.array: subset type $Is
axiom (forall _System.array$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array(_System.array$arg)) } 
  $Is(c#0, Tclass._System.array(_System.array$arg))
     <==> $Is(c#0, Tclass._System.array?(_System.array$arg)) && c#0 != null);

// _System.array: subset type $IsAlloc
axiom (forall _System.array$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array?(_System.array$arg), $h));

function Tclass._System.___hFunc1(Ty, Ty) : Ty;

// Tclass._System.___hFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hFunc1(#$T0, #$R)) == Tagclass._System.___hFunc1);

const unique Tagclass._System.___hFunc1: TyTag;

// Tclass._System.___hFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_0(Tclass._System.___hFunc1(#$T0, #$R)) == #$T0);

function Tclass._System.___hFunc1_0(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_1(Tclass._System.___hFunc1(#$T0, #$R)) == #$R);

function Tclass._System.___hFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc1(#$T0, #$R)));

function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set Box) : HandleType;

function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

function Reads1(Ty, Ty, Heap, HandleType, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box :: 
  { Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) == h[heap, bx0]);

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box :: 
  { Requires1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box, 
    bx: Box :: 
  { Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] } 
  Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] == rd[heap, bx0][bx]);

function {:inline} Requires1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

function {:inline} Reads1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// empty-reads property for Reads1 
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Reads1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Reads1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap) && $IsBox(bx0, t0) && $Is(f, Tclass._System.___hFunc1(t0, t1))
     ==> (Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
       <==> Set#Equal(Reads1(t0, t1, heap, f, bx0), Set#Empty(): Set Box)));

// empty-reads property for Requires1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Requires1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Requires1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
     ==> Requires1(t0, t1, $OneHeap, f, bx0) == Requires1(t0, t1, heap, f, bx0));

axiom (forall f: HandleType, t0: Ty, t1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
     <==> (forall h: Heap, bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsGoodHeap(h) && $IsBox(bx0, t0) && Requires1(t0, t1, h, f, bx0)
         ==> $IsBox(Apply1(t0, t1, h, f, bx0), t1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t1) } { $IsBox(bx, u1) } 
        $IsBox(bx, t1) ==> $IsBox(bx, u1))
     ==> $Is(f, Tclass._System.___hFunc1(u0, u1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
       <==> (forall bx0: Box :: 
        { Apply1(t0, t1, h, f, bx0) } { Reads1(t0, t1, h, f, bx0) } 
        $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
           ==> (forall r: ref :: 
            { Reads1(t0, t1, h, f, bx0)[$Box(r)] } 
            r != null && Reads1(t0, t1, h, f, bx0)[$Box(r)] ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
     ==> (forall bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
         ==> $IsAllocBox(Apply1(t0, t1, h, f, bx0), t1, h)));

function Tclass._System.___hPartialFunc1(Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == Tagclass._System.___hPartialFunc1);

const unique Tagclass._System.___hPartialFunc1: TyTag;

// Tclass._System.___hPartialFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_0(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_1(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$R);

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc1(#$T0, #$R)));

// _System._#PartialFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc1(#$T0, #$R))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0)
           ==> Set#Equal(Reads1(#$T0, #$R, $OneHeap, f#0, x0#0), Set#Empty(): Set Box)));

// _System._#PartialFunc1: subset type $IsAlloc
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc1(#$T0, #$R), $h));

function Tclass._System.___hTotalFunc1(Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hTotalFunc1(#$T0, #$R)) == Tagclass._System.___hTotalFunc1);

const unique Tagclass._System.___hTotalFunc1: TyTag;

// Tclass._System.___hTotalFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_0(Tclass._System.___hTotalFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_1(Tclass._System.___hTotalFunc1(#$T0, #$R)) == #$R);

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// _System._#TotalFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)));

// _System._#TotalFunc1: subset type $IsAlloc
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h));

function Tclass._System.___hFunc0(Ty) : Ty;

// Tclass._System.___hFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tag(Tclass._System.___hFunc0(#$R)) == Tagclass._System.___hFunc0);

const unique Tagclass._System.___hFunc0: TyTag;

// Tclass._System.___hFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tclass._System.___hFunc0_0(Tclass._System.___hFunc0(#$R)) == #$R);

function Tclass._System.___hFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc0(#$R)));

function Handle0([Heap]Box, [Heap]bool, [Heap]Set Box) : HandleType;

function Apply0(Ty, Heap, HandleType) : Box;

function Requires0(Ty, Heap, HandleType) : bool;

function Reads0(Ty, Heap, HandleType) : Set Box;

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box :: 
  { Apply0(t0, heap, Handle0(h, r, rd)) } 
  Apply0(t0, heap, Handle0(h, r, rd)) == h[heap]);

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box :: 
  { Requires0(t0, heap, Handle0(h, r, rd)) } 
  r[heap] ==> Requires0(t0, heap, Handle0(h, r, rd)));

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box, bx: Box :: 
  { Reads0(t0, heap, Handle0(h, r, rd))[bx] } 
  Reads0(t0, heap, Handle0(h, r, rd))[bx] == rd[heap][bx]);

function {:inline} Requires0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

function {:inline} Reads0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// empty-reads property for Reads0 
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Reads0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Reads0(t0, heap, f) } 
  $IsGoodHeap(heap) && $Is(f, Tclass._System.___hFunc0(t0))
     ==> (Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
       <==> Set#Equal(Reads0(t0, heap, f), Set#Empty(): Set Box)));

// empty-reads property for Requires0
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Requires0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Requires0(t0, heap, f) } 
  $IsGoodHeap(heap)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
     ==> Requires0(t0, $OneHeap, f) == Requires0(t0, heap, f));

axiom (forall f: HandleType, t0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
     <==> (forall h: Heap :: 
      { Apply0(t0, h, f) } 
      $IsGoodHeap(h) && Requires0(t0, h, f) ==> $IsBox(Apply0(t0, h, f), t0)));

axiom (forall f: HandleType, t0: Ty, u0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)), $Is(f, Tclass._System.___hFunc0(u0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t0) } { $IsBox(bx, u0) } 
        $IsBox(bx, t0) ==> $IsBox(bx, u0))
     ==> $Is(f, Tclass._System.___hFunc0(u0)));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc0(t0), h)
       <==> Requires0(t0, h, f)
         ==> (forall r: ref :: 
          { Reads0(t0, h, f)[$Box(r)] } 
          r != null && Reads0(t0, h, f)[$Box(r)] ==> read(h, r, alloc))));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc0(t0), h)
     ==> 
    Requires0(t0, h, f)
     ==> $IsAllocBox(Apply0(t0, h, f), t0, h));

function Tclass._System.___hPartialFunc0(Ty) : Ty;

// Tclass._System.___hPartialFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tag(Tclass._System.___hPartialFunc0(#$R)) == Tagclass._System.___hPartialFunc0);

const unique Tagclass._System.___hPartialFunc0: TyTag;

// Tclass._System.___hPartialFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tclass._System.___hPartialFunc0_0(Tclass._System.___hPartialFunc0(#$R)) == #$R);

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc0(#$R)));

// _System._#PartialFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hFunc0(#$R))
       && Set#Equal(Reads0(#$R, $OneHeap, f#0), Set#Empty(): Set Box));

// _System._#PartialFunc0: subset type $IsAlloc
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc0(#$R), $h));

function Tclass._System.___hTotalFunc0(Ty) : Ty;

// Tclass._System.___hTotalFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tag(Tclass._System.___hTotalFunc0(#$R)) == Tagclass._System.___hTotalFunc0);

const unique Tagclass._System.___hTotalFunc0: TyTag;

// Tclass._System.___hTotalFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tclass._System.___hTotalFunc0_0(Tclass._System.___hTotalFunc0(#$R)) == #$R);

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc0(#$R)));

// _System._#TotalFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) && Requires0(#$R, $OneHeap, f#0));

// _System._#TotalFunc0: subset type $IsAlloc
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h));

function Tclass._System.___hFunc2(Ty, Ty, Ty) : Ty;

// Tclass._System.___hFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == Tagclass._System.___hFunc2);

const unique Tagclass._System.___hFunc2: TyTag;

// Tclass._System.___hFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_0(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T0);

function Tclass._System.___hFunc2_0(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_1(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T1);

function Tclass._System.___hFunc2_1(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_2(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$R);

function Tclass._System.___hFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc2(#$T0, #$T1, #$R)));

function Handle2([Heap,Box,Box]Box, [Heap,Box,Box]bool, [Heap,Box,Box]Set Box) : HandleType;

function Apply2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Box;

function Requires2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : bool;

function Reads2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box :: 
  { Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) } 
  Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) == h[heap, bx0, bx1]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box :: 
  { Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) } 
  r[heap, bx0, bx1] ==> Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx: Box :: 
  { Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1)[bx] } 
  Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1)[bx]
     == rd[heap, bx0, bx1][bx]);

function {:inline} Requires2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

function {:inline} Reads2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// empty-reads property for Reads2 
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) } 
    { Reads2(t0, t1, t2, heap, f, bx0, bx1) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     ==> (Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set Box)
       <==> Set#Equal(Reads2(t0, t1, t2, heap, f, bx0, bx1), Set#Empty(): Set Box)));

// empty-reads property for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) } 
    { Requires2(t0, t1, t2, heap, f, bx0, bx1) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set Box)
     ==> Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1)
       == Requires2(t0, t1, t2, heap, f, bx0, bx1));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty :: 
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)) } 
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     <==> (forall h: Heap, bx0: Box, bx1: Box :: 
      { Apply2(t0, t1, t2, h, f, bx0, bx1) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, u0: Ty, u1: Ty, u2: Ty :: 
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)), $Is(f, Tclass._System.___hFunc2(u0, u1, u2)) } 
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, u1) } { $IsBox(bx, t1) } 
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, t2) } { $IsBox(bx, u2) } 
        $IsBox(bx, t2) ==> $IsBox(bx, u2))
     ==> $Is(f, Tclass._System.___hFunc2(u0, u1, u2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
       <==> (forall bx0: Box, bx1: Box :: 
        { Apply2(t0, t1, t2, h, f, bx0, bx1) } { Reads2(t0, t1, t2, h, f, bx0, bx1) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && Requires2(t0, t1, t2, h, f, bx0, bx1)
           ==> (forall r: ref :: 
            { Reads2(t0, t1, t2, h, f, bx0, bx1)[$Box(r)] } 
            r != null && Reads2(t0, t1, t2, h, f, bx0, bx1)[$Box(r)] ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
     ==> (forall bx0: Box, bx1: Box :: 
      { Apply2(t0, t1, t2, h, f, bx0, bx1) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsAllocBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2, h)));

function Tclass._System.___hPartialFunc2(Ty, Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == Tagclass._System.___hPartialFunc2);

const unique Tagclass._System.___hPartialFunc2: TyTag;

// Tclass._System.___hPartialFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_0(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc2_0(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_1(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc2_1(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_2(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$R);

function Tclass._System.___hPartialFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)));

// _System._#PartialFunc2: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
       && (forall x0#0: Box, x1#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Set#Equal(Reads2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0), Set#Empty(): Set Box)));

// _System._#PartialFunc2: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R), $h));

function Tclass._System.___hTotalFunc2(Ty, Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == Tagclass._System.___hTotalFunc2);

const unique Tagclass._System.___hTotalFunc2: TyTag;

// Tclass._System.___hTotalFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_0(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc2_0(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_1(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc2_1(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_2(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$R);

function Tclass._System.___hTotalFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)));

// _System._#TotalFunc2: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       && (forall x0#0: Box, x1#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Requires2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0)));

// _System._#TotalFunc2: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h));

function Tclass._System.___hFunc3(Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tag(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == Tagclass._System.___hFunc3);

const unique Tagclass._System.___hFunc3: TyTag;

// Tclass._System.___hFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_0(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hFunc3_0(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_1(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hFunc3_1(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_2(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hFunc3_2(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_3(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)));

function Handle3([Heap,Box,Box,Box]Box, [Heap,Box,Box,Box]bool, [Heap,Box,Box,Box]Set Box)
   : HandleType;

function Apply3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Box;

function Requires3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : bool;

function Reads3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) } 
  Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)
     == h[heap, bx0, bx1, bx2]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) } 
  r[heap, bx0, bx1, bx2]
     ==> Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx: Box :: 
  { Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx] } 
  Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx]
     == rd[heap, bx0, bx1, bx2][bx]);

function {:inline} Requires3#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box)
   : bool
{
  true
}

function {:inline} Reads3#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box)
   : bool
{
  true
}

// frame axiom for Reads3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Reads3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// empty-reads property for Reads3 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) } 
    { Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     ==> (Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
       <==> Set#Equal(Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2), Set#Empty(): Set Box)));

// empty-reads property for Requires3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) } 
    { Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
     ==> Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty :: 
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)) } 
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box :: 
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, u0: Ty, u1: Ty, u2: Ty, u3: Ty :: 
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)), $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)) } 
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, u1) } { $IsBox(bx, t1) } 
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, u2) } { $IsBox(bx, t2) } 
        $IsBox(bx, u2) ==> $IsBox(bx, t2))
       && (forall bx: Box :: 
        { $IsBox(bx, t3) } { $IsBox(bx, u3) } 
        $IsBox(bx, t3) ==> $IsBox(bx, u3))
     ==> $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box :: 
        { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
          { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && 
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
           ==> (forall r: ref :: 
            { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)] } 
            r != null && Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box :: 
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsAllocBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3, h)));

function Tclass._System.___hPartialFunc3(Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tag(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == Tagclass._System.___hPartialFunc3);

const unique Tagclass._System.___hPartialFunc3: TyTag;

// Tclass._System.___hPartialFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_0(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc3_0(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_1(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc3_1(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_2(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc3_2(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_3(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hPartialFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#PartialFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Set#Equal(Reads3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R), $h));

function Tclass._System.___hTotalFunc3(Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tag(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == Tagclass._System.___hTotalFunc3);

const unique Tagclass._System.___hTotalFunc3: TyTag;

// Tclass._System.___hTotalFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_0(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc3_0(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_1(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc3_1(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_2(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc3_2(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_3(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hTotalFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#TotalFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Requires3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0)));

// _System._#TotalFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h));

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType;

const unique ##_System._tuple#0._#Make0: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;

function _System.Tuple0.___hMake0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#0._#Make0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d) ==> d == #_System._tuple#0._#Make0());

function Tclass._System.Tuple0() : Ty;

// Tclass._System.Tuple0 Tag
axiom Tag(Tclass._System.Tuple0()) == Tagclass._System.Tuple0;

const unique Tagclass._System.Tuple0: TyTag;

// Box/unbox axiom for Tclass._System.Tuple0
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple0()) } 
  $IsBox(bx, Tclass._System.Tuple0())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.Tuple0()));

// Constructor $Is
axiom $Is(#_System._tuple#0._#Make0(), Tclass._System.Tuple0());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.Tuple0(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.Tuple0(), $h));

// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit(#_System._tuple#0._#Make0());

// Depth-one case-split function
function $IsA#_System.Tuple0(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple0(d) } 
  $IsA#_System.Tuple0(d) ==> _System.Tuple0.___hMake0_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d), $Is(d, Tclass._System.Tuple0()) } 
  $Is(d, Tclass._System.Tuple0()) ==> _System.Tuple0.___hMake0_q(d));

// Datatype extensional equality declaration
function _System.Tuple0#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#0._#Make0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  true ==> (_System.Tuple0#Equal(a, b) <==> true));

// Datatype extensionality axiom: _System._tuple#0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b) <==> a == b);

const unique class._System.Tuple0: ClassName;

function Tclass._System.___hFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tag(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == Tagclass._System.___hFunc5);

const unique Tagclass._System.___hFunc5: TyTag;

// Tclass._System.___hFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_0(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hFunc5_0(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_1(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hFunc5_1(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_2(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hFunc5_2(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_3(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hFunc5_3(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_4(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hFunc5_4(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_5(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

function Handle5([Heap,Box,Box,Box,Box,Box]Box, 
    [Heap,Box,Box,Box,Box,Box]bool, 
    [Heap,Box,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : Box;

function Requires5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : bool;

function Reads5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Apply5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4) } 
  Apply5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)
     == h[heap, bx0, bx1, bx2, bx3, bx4]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Requires5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4) } 
  r[heap, bx0, bx1, bx2, bx3, bx4]
     ==> Requires5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx: Box :: 
  { Reads5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)[bx] } 
  Reads5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)[bx]
     == rd[heap, bx0, bx1, bx2, bx3, bx4][bx]);

function {:inline} Requires5#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box)
   : bool
{
  true
}

function {:inline} Reads5#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box)
   : bool
{
  true
}

// frame axiom for Reads5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Reads5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Requires5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Requires5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Apply5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Apply5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// empty-reads property for Reads5 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), $IsGoodHeap(heap) } 
    { Reads5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
     ==> (Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), 
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4), 
        Set#Empty(): Set Box)));

// empty-reads property for Requires5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Requires5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), $IsGoodHeap(heap) } 
    { Requires5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), 
        Set#Empty(): Set Box)
     ==> Requires5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty :: 
  { $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5)) } 
  $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box :: 
      { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && $IsBox(bx4, t4)
           && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
         ==> $IsBox(Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4), t5)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    u0: Ty, 
    u1: Ty, 
    u2: Ty, 
    u3: Ty, 
    u4: Ty, 
    u5: Ty :: 
  { $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5)), $Is(f, Tclass._System.___hFunc5(u0, u1, u2, u3, u4, u5)) } 
  $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, u1) } { $IsBox(bx, t1) } 
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, u2) } { $IsBox(bx, t2) } 
        $IsBox(bx, u2) ==> $IsBox(bx, t2))
       && (forall bx: Box :: 
        { $IsBox(bx, u3) } { $IsBox(bx, t3) } 
        $IsBox(bx, u3) ==> $IsBox(bx, t3))
       && (forall bx: Box :: 
        { $IsBox(bx, u4) } { $IsBox(bx, t4) } 
        $IsBox(bx, u4) ==> $IsBox(bx, t4))
       && (forall bx: Box :: 
        { $IsBox(bx, t5) } { $IsBox(bx, u5) } 
        $IsBox(bx, t5) ==> $IsBox(bx, u5))
     ==> $Is(f, Tclass._System.___hFunc5(u0, u1, u2, u3, u4, u5)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box :: 
        { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
          { Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && 
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && 
            $IsBox(bx3, t3)
             && $IsAllocBox(bx3, t3, h)
             && 
            $IsBox(bx4, t4)
             && $IsAllocBox(bx4, t4, h)
             && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
           ==> (forall r: ref :: 
            { Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)[$Box(r)] } 
            r != null
                 && Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h) } 
  $IsGoodHeap(h)
       && $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box :: 
      { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && $IsAllocBox(bx4, t4, h)
           && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
         ==> $IsAllocBox(Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4), t5, h)));

function Tclass._System.___hPartialFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hPartialFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tag(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == Tagclass._System.___hPartialFunc5);

const unique Tagclass._System.___hPartialFunc5: TyTag;

// Tclass._System.___hPartialFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_0(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc5_0(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_1(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc5_1(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_2(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc5_2(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_3(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hPartialFunc5_3(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_4(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hPartialFunc5_4(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_5(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hPartialFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

// _System._#PartialFunc5: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box, x4#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
           ==> Set#Equal(Reads5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0, x4#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc5: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h));

function Tclass._System.___hTotalFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

// Tclass._System.___hTotalFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tag(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == Tagclass._System.___hTotalFunc5);

const unique Tagclass._System.___hTotalFunc5: TyTag;

// Tclass._System.___hTotalFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_0(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc5_0(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_1(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc5_1(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_2(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc5_2(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_3(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hTotalFunc5_3(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_4(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hTotalFunc5_4(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_5(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hTotalFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

// _System._#TotalFunc5: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box, x4#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
           ==> Requires5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0, x4#0)));

// _System._#TotalFunc5: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h));

// Constructor function declaration
function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

const unique ##_System._tuple#2._#Make2: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0))
     == ##_System._tuple#2._#Make2);

function _System.Tuple2.___hMake2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#2._#Make2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: Box :: 
      d == #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)));

function Tclass._System.Tuple2(Ty, Ty) : Ty;

// Tclass._System.Tuple2 Tag
axiom (forall #$T0: Ty, #$T1: Ty :: 
  { Tclass._System.Tuple2(#$T0, #$T1) } 
  Tag(Tclass._System.Tuple2(#$T0, #$T1)) == Tagclass._System.Tuple2);

const unique Tagclass._System.Tuple2: TyTag;

// Tclass._System.Tuple2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty :: 
  { Tclass._System.Tuple2(#$T0, #$T1) } 
  Tclass._System.Tuple2_0(Tclass._System.Tuple2(#$T0, #$T1)) == #$T0);

function Tclass._System.Tuple2_0(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty :: 
  { Tclass._System.Tuple2(#$T0, #$T1) } 
  Tclass._System.Tuple2_1(Tclass._System.Tuple2(#$T0, #$T1)) == #$T1);

function Tclass._System.Tuple2_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.Tuple2
axiom (forall #$T0: Ty, #$T1: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple2(#$T0, #$T1)) } 
  $IsBox(bx, Tclass._System.Tuple2(#$T0, #$T1))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.Tuple2(#$T0, #$T1)));

// Constructor $Is
axiom (forall #$T0: Ty, #$T1: Ty, a#7#0#0: Box, a#7#1#0: Box :: 
  { $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0), Tclass._System.Tuple2(#$T0, #$T1)) } 
  $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0), Tclass._System.Tuple2(#$T0, #$T1))
     <==> $IsBox(a#7#0#0, #$T0) && $IsBox(a#7#1#0, #$T1));

// Constructor $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, a#8#0#0: Box, a#8#1#0: Box, $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0), 
      Tclass._System.Tuple2(#$T0, #$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0), 
        Tclass._System.Tuple2(#$T0, #$T1), 
        $h)
       <==> $IsAllocBox(a#8#0#0, #$T0, $h) && $IsAllocBox(a#8#1#0, #$T1, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, #$T0: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._0(d), #$T0, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists #$T1: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(#$T0, #$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(#$T0, #$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._0(d), #$T0, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, #$T1: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._1(d), #$T1, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists #$T0: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(#$T0, #$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(#$T0, #$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._1(d), #$T1, $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_System._tuple#2._#Make2(a#9#0#0, a#9#1#0)));

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#10#0#0, a#10#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#_System._tuple#2._#Make2(a#11#0#0, a#11#1#0)));

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#12#0#0, a#12#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#13#0#0, a#13#1#0) } 
  BoxRank(a#13#1#0) < DtRank(#_System._tuple#2._#Make2(a#13#0#0, a#13#1#0)));

// Depth-one case-split function
function $IsA#_System.Tuple2(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple2(d) } 
  $IsA#_System.Tuple2(d) ==> _System.Tuple2.___hMake2_q(d));

// Questionmark data type disjunctivity
axiom (forall #$T0: Ty, #$T1: Ty, d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d), $Is(d, Tclass._System.Tuple2(#$T0, #$T1)) } 
  $Is(d, Tclass._System.Tuple2(#$T0, #$T1)) ==> _System.Tuple2.___hMake2_q(d));

// Datatype extensional equality declaration
function _System.Tuple2#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#2._#Make2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  true
     ==> (_System.Tuple2#Equal(a, b)
       <==> _System.Tuple2._0(a) == _System.Tuple2._0(b)
         && _System.Tuple2._1(a) == _System.Tuple2._1(b)));

// Datatype extensionality axiom: _System._tuple#2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b) <==> a == b);

const unique class._System.Tuple2: ClassName;

// Constructor function declaration
function #_module.Option.None() : DatatypeType;

const unique ##_module.Option.None: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Option.None()) == ##_module.Option.None;

function _module.Option.None_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Option.None_q(d) } 
  _module.Option.None_q(d) <==> DatatypeCtorId(d) == ##_module.Option.None);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Option.None_q(d) } 
  _module.Option.None_q(d) ==> d == #_module.Option.None());

function Tclass._module.Option(Ty) : Ty;

// Tclass._module.Option Tag
axiom (forall _module.Option$V: Ty :: 
  { Tclass._module.Option(_module.Option$V) } 
  Tag(Tclass._module.Option(_module.Option$V)) == Tagclass._module.Option);

const unique Tagclass._module.Option: TyTag;

// Tclass._module.Option injectivity 0
axiom (forall _module.Option$V: Ty :: 
  { Tclass._module.Option(_module.Option$V) } 
  Tclass._module.Option_0(Tclass._module.Option(_module.Option$V))
     == _module.Option$V);

function Tclass._module.Option_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Option
axiom (forall _module.Option$V: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Option(_module.Option$V)) } 
  $IsBox(bx, Tclass._module.Option(_module.Option$V))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Option(_module.Option$V)));

// Constructor $Is
axiom (forall _module.Option$V: Ty :: 
  { $Is(#_module.Option.None(), Tclass._module.Option(_module.Option$V)) } 
  $Is(#_module.Option.None(), Tclass._module.Option(_module.Option$V)));

// Constructor $IsAlloc
axiom (forall _module.Option$V: Ty, $h: Heap :: 
  { $IsAlloc(#_module.Option.None(), Tclass._module.Option(_module.Option$V), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Option.None(), Tclass._module.Option(_module.Option$V), $h));

// Constructor literal
axiom #_module.Option.None() == Lit(#_module.Option.None());

// Constructor function declaration
function #_module.Option.Some(Box) : DatatypeType;

const unique ##_module.Option.Some: DtCtorId;

// Constructor identifier
axiom (forall a#19#0#0: Box :: 
  { #_module.Option.Some(a#19#0#0) } 
  DatatypeCtorId(#_module.Option.Some(a#19#0#0)) == ##_module.Option.Some);

function _module.Option.Some_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Option.Some_q(d) } 
  _module.Option.Some_q(d) <==> DatatypeCtorId(d) == ##_module.Option.Some);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Option.Some_q(d) } 
  _module.Option.Some_q(d)
     ==> (exists a#20#0#0: Box :: d == #_module.Option.Some(a#20#0#0)));

// Constructor $Is
axiom (forall _module.Option$V: Ty, a#21#0#0: Box :: 
  { $Is(#_module.Option.Some(a#21#0#0), Tclass._module.Option(_module.Option$V)) } 
  $Is(#_module.Option.Some(a#21#0#0), Tclass._module.Option(_module.Option$V))
     <==> $IsBox(a#21#0#0, _module.Option$V));

// Constructor $IsAlloc
axiom (forall _module.Option$V: Ty, a#22#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Option.Some(a#22#0#0), Tclass._module.Option(_module.Option$V), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Option.Some(a#22#0#0), Tclass._module.Option(_module.Option$V), $h)
       <==> $IsAllocBox(a#22#0#0, _module.Option$V, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Option$V: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Option.value(d), _module.Option$V, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Option.Some_q(d)
       && $IsAlloc(d, Tclass._module.Option(_module.Option$V), $h)
     ==> $IsAllocBox(_module.Option.value(d), _module.Option$V, $h));

// Constructor literal
axiom (forall a#23#0#0: Box :: 
  { #_module.Option.Some(Lit(a#23#0#0)) } 
  #_module.Option.Some(Lit(a#23#0#0)) == Lit(#_module.Option.Some(a#23#0#0)));

function _module.Option.value(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#24#0#0: Box :: 
  { #_module.Option.Some(a#24#0#0) } 
  _module.Option.value(#_module.Option.Some(a#24#0#0)) == a#24#0#0);

// Inductive rank
axiom (forall a#25#0#0: Box :: 
  { #_module.Option.Some(a#25#0#0) } 
  BoxRank(a#25#0#0) < DtRank(#_module.Option.Some(a#25#0#0)));

// Depth-one case-split function
function $IsA#_module.Option(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Option(d) } 
  $IsA#_module.Option(d) ==> _module.Option.None_q(d) || _module.Option.Some_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Option$V: Ty, d: DatatypeType :: 
  { _module.Option.Some_q(d), $Is(d, Tclass._module.Option(_module.Option$V)) } 
    { _module.Option.None_q(d), $Is(d, Tclass._module.Option(_module.Option$V)) } 
  $Is(d, Tclass._module.Option(_module.Option$V))
     ==> _module.Option.None_q(d) || _module.Option.Some_q(d));

// Datatype extensional equality declaration
function _module.Option#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Option.None
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Option#Equal(a, b), _module.Option.None_q(a) } 
    { _module.Option#Equal(a, b), _module.Option.None_q(b) } 
  _module.Option.None_q(a) && _module.Option.None_q(b)
     ==> (_module.Option#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Option.Some
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Option#Equal(a, b), _module.Option.Some_q(a) } 
    { _module.Option#Equal(a, b), _module.Option.Some_q(b) } 
  _module.Option.Some_q(a) && _module.Option.Some_q(b)
     ==> (_module.Option#Equal(a, b)
       <==> _module.Option.value(a) == _module.Option.value(b)));

// Datatype extensionality axiom: _module.Option
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Option#Equal(a, b) } 
  _module.Option#Equal(a, b) <==> a == b);

const unique class._module.Option: ClassName;

// Constructor function declaration
function #_module.Node.Node(DatatypeType, int, int) : DatatypeType;

const unique ##_module.Node.Node: DtCtorId;

// Constructor identifier
axiom (forall a#26#0#0: DatatypeType, a#26#1#0: int, a#26#2#0: int :: 
  { #_module.Node.Node(a#26#0#0, a#26#1#0, a#26#2#0) } 
  DatatypeCtorId(#_module.Node.Node(a#26#0#0, a#26#1#0, a#26#2#0))
     == ##_module.Node.Node);

function _module.Node.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Node.Node_q(d) } 
  _module.Node.Node_q(d) <==> DatatypeCtorId(d) == ##_module.Node.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Node.Node_q(d) } 
  _module.Node.Node_q(d)
     ==> (exists a#27#0#0: DatatypeType, a#27#1#0: int, a#27#2#0: int :: 
      d == #_module.Node.Node(a#27#0#0, a#27#1#0, a#27#2#0)));

function Tclass._module.Node(Ty) : Ty;

// Tclass._module.Node Tag
axiom (forall _module.Node$A: Ty :: 
  { Tclass._module.Node(_module.Node$A) } 
  Tag(Tclass._module.Node(_module.Node$A)) == Tagclass._module.Node);

const unique Tagclass._module.Node: TyTag;

// Tclass._module.Node injectivity 0
axiom (forall _module.Node$A: Ty :: 
  { Tclass._module.Node(_module.Node$A) } 
  Tclass._module.Node_0(Tclass._module.Node(_module.Node$A)) == _module.Node$A);

function Tclass._module.Node_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Node
axiom (forall _module.Node$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Node(_module.Node$A)) } 
  $IsBox(bx, Tclass._module.Node(_module.Node$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Node(_module.Node$A)));

// Constructor $Is
axiom (forall _module.Node$A: Ty, a#28#0#0: DatatypeType, a#28#1#0: int, a#28#2#0: int :: 
  { $Is(#_module.Node.Node(a#28#0#0, a#28#1#0, a#28#2#0), 
      Tclass._module.Node(_module.Node$A)) } 
  $Is(#_module.Node.Node(a#28#0#0, a#28#1#0, a#28#2#0), 
      Tclass._module.Node(_module.Node$A))
     <==> $Is(a#28#0#0, Tclass._module.Option(_module.Node$A))
       && $Is(a#28#1#0, TInt)
       && $Is(a#28#2#0, TInt));

// Constructor $IsAlloc
axiom (forall _module.Node$A: Ty, 
    a#29#0#0: DatatypeType, 
    a#29#1#0: int, 
    a#29#2#0: int, 
    $h: Heap :: 
  { $IsAlloc(#_module.Node.Node(a#29#0#0, a#29#1#0, a#29#2#0), 
      Tclass._module.Node(_module.Node$A), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Node.Node(a#29#0#0, a#29#1#0, a#29#2#0), 
        Tclass._module.Node(_module.Node$A), 
        $h)
       <==> $IsAlloc(a#29#0#0, Tclass._module.Option(_module.Node$A), $h)
         && $IsAlloc(a#29#1#0, TInt, $h)
         && $IsAlloc(a#29#2#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Node$A: Ty, $h: Heap :: 
  { $IsAlloc(_module.Node.data(d), Tclass._module.Option(_module.Node$A), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Node.Node_q(d)
       && $IsAlloc(d, Tclass._module.Node(_module.Node$A), $h)
     ==> $IsAlloc(_module.Node.data(d), Tclass._module.Option(_module.Node$A), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Node.next(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Node.Node_q(d)
       && (exists _module.Node$A: Ty :: 
        { $IsAlloc(d, Tclass._module.Node(_module.Node$A), $h) } 
        $IsAlloc(d, Tclass._module.Node(_module.Node$A), $h))
     ==> $IsAlloc(_module.Node.next(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Node.prev(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Node.Node_q(d)
       && (exists _module.Node$A: Ty :: 
        { $IsAlloc(d, Tclass._module.Node(_module.Node$A), $h) } 
        $IsAlloc(d, Tclass._module.Node(_module.Node$A), $h))
     ==> $IsAlloc(_module.Node.prev(d), TInt, $h));

// Constructor literal
axiom (forall a#30#0#0: DatatypeType, a#30#1#0: int, a#30#2#0: int :: 
  { #_module.Node.Node(Lit(a#30#0#0), LitInt(a#30#1#0), LitInt(a#30#2#0)) } 
  #_module.Node.Node(Lit(a#30#0#0), LitInt(a#30#1#0), LitInt(a#30#2#0))
     == Lit(#_module.Node.Node(a#30#0#0, a#30#1#0, a#30#2#0)));

function _module.Node.data(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#31#0#0: DatatypeType, a#31#1#0: int, a#31#2#0: int :: 
  { #_module.Node.Node(a#31#0#0, a#31#1#0, a#31#2#0) } 
  _module.Node.data(#_module.Node.Node(a#31#0#0, a#31#1#0, a#31#2#0)) == a#31#0#0);

// Inductive rank
axiom (forall a#32#0#0: DatatypeType, a#32#1#0: int, a#32#2#0: int :: 
  { #_module.Node.Node(a#32#0#0, a#32#1#0, a#32#2#0) } 
  DtRank(a#32#0#0) < DtRank(#_module.Node.Node(a#32#0#0, a#32#1#0, a#32#2#0)));

function _module.Node.next(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#33#0#0: DatatypeType, a#33#1#0: int, a#33#2#0: int :: 
  { #_module.Node.Node(a#33#0#0, a#33#1#0, a#33#2#0) } 
  _module.Node.next(#_module.Node.Node(a#33#0#0, a#33#1#0, a#33#2#0)) == a#33#1#0);

function _module.Node.prev(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#34#0#0: DatatypeType, a#34#1#0: int, a#34#2#0: int :: 
  { #_module.Node.Node(a#34#0#0, a#34#1#0, a#34#2#0) } 
  _module.Node.prev(#_module.Node.Node(a#34#0#0, a#34#1#0, a#34#2#0)) == a#34#2#0);

// Depth-one case-split function
function $IsA#_module.Node(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Node(d) } 
  $IsA#_module.Node(d) ==> _module.Node.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Node$A: Ty, d: DatatypeType :: 
  { _module.Node.Node_q(d), $Is(d, Tclass._module.Node(_module.Node$A)) } 
  $Is(d, Tclass._module.Node(_module.Node$A)) ==> _module.Node.Node_q(d));

// Datatype extensional equality declaration
function _module.Node#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Node.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Node#Equal(a, b) } 
  true
     ==> (_module.Node#Equal(a, b)
       <==> _module.Option#Equal(_module.Node.data(a), _module.Node.data(b))
         && _module.Node.next(a) == _module.Node.next(b)
         && _module.Node.prev(a) == _module.Node.prev(b)));

// Datatype extensionality axiom: _module.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Node#Equal(a, b) } 
  _module.Node#Equal(a, b) <==> a == b);

const unique class._module.Node: ClassName;

// Constructor function declaration
function #_module.DList.DList(Seq Box, int, Seq Box, Seq Box, Seq Box) : DatatypeType;

const unique ##_module.DList.DList: DtCtorId;

// Constructor identifier
axiom (forall a#35#0#0: Seq Box, 
    a#35#1#0: int, 
    a#35#2#0: Seq Box, 
    a#35#3#0: Seq Box, 
    a#35#4#0: Seq Box :: 
  { #_module.DList.DList(a#35#0#0, a#35#1#0, a#35#2#0, a#35#3#0, a#35#4#0) } 
  DatatypeCtorId(#_module.DList.DList(a#35#0#0, a#35#1#0, a#35#2#0, a#35#3#0, a#35#4#0))
     == ##_module.DList.DList);

function _module.DList.DList_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.DList.DList_q(d) } 
  _module.DList.DList_q(d) <==> DatatypeCtorId(d) == ##_module.DList.DList);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.DList.DList_q(d) } 
  _module.DList.DList_q(d)
     ==> (exists a#36#0#0: Seq Box, 
        a#36#1#0: int, 
        a#36#2#0: Seq Box, 
        a#36#3#0: Seq Box, 
        a#36#4#0: Seq Box :: 
      d == #_module.DList.DList(a#36#0#0, a#36#1#0, a#36#2#0, a#36#3#0, a#36#4#0)));

function Tclass._module.DList(Ty) : Ty;

// Tclass._module.DList Tag
axiom (forall _module.DList$A: Ty :: 
  { Tclass._module.DList(_module.DList$A) } 
  Tag(Tclass._module.DList(_module.DList$A)) == Tagclass._module.DList);

const unique Tagclass._module.DList: TyTag;

// Tclass._module.DList injectivity 0
axiom (forall _module.DList$A: Ty :: 
  { Tclass._module.DList(_module.DList$A) } 
  Tclass._module.DList_0(Tclass._module.DList(_module.DList$A)) == _module.DList$A);

function Tclass._module.DList_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.DList
axiom (forall _module.DList$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.DList(_module.DList$A)) } 
  $IsBox(bx, Tclass._module.DList(_module.DList$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.DList(_module.DList$A)));

// Constructor $Is
axiom (forall _module.DList$A: Ty, 
    a#37#0#0: Seq Box, 
    a#37#1#0: int, 
    a#37#2#0: Seq Box, 
    a#37#3#0: Seq Box, 
    a#37#4#0: Seq Box :: 
  { $Is(#_module.DList.DList(a#37#0#0, a#37#1#0, a#37#2#0, a#37#3#0, a#37#4#0), 
      Tclass._module.DList(_module.DList$A)) } 
  $Is(#_module.DList.DList(a#37#0#0, a#37#1#0, a#37#2#0, a#37#3#0, a#37#4#0), 
      Tclass._module.DList(_module.DList$A))
     <==> $Is(a#37#0#0, TSeq(Tclass._module.Node(_module.DList$A)))
       && $Is(a#37#1#0, TInt)
       && $Is(a#37#2#0, TSeq(_module.DList$A))
       && $Is(a#37#3#0, TSeq(TInt))
       && $Is(a#37#4#0, TSeq(TInt)));

// Constructor $IsAlloc
axiom (forall _module.DList$A: Ty, 
    a#38#0#0: Seq Box, 
    a#38#1#0: int, 
    a#38#2#0: Seq Box, 
    a#38#3#0: Seq Box, 
    a#38#4#0: Seq Box, 
    $h: Heap :: 
  { $IsAlloc(#_module.DList.DList(a#38#0#0, a#38#1#0, a#38#2#0, a#38#3#0, a#38#4#0), 
      Tclass._module.DList(_module.DList$A), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.DList.DList(a#38#0#0, a#38#1#0, a#38#2#0, a#38#3#0, a#38#4#0), 
        Tclass._module.DList(_module.DList$A), 
        $h)
       <==> $IsAlloc(a#38#0#0, TSeq(Tclass._module.Node(_module.DList$A)), $h)
         && $IsAlloc(a#38#1#0, TInt, $h)
         && $IsAlloc(a#38#2#0, TSeq(_module.DList$A), $h)
         && $IsAlloc(a#38#3#0, TSeq(TInt), $h)
         && $IsAlloc(a#38#4#0, TSeq(TInt), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.DList$A: Ty, $h: Heap :: 
  { $IsAlloc(_module.DList.nodes(d), TSeq(Tclass._module.Node(_module.DList$A)), $h) } 
  $IsGoodHeap($h)
       && 
      _module.DList.DList_q(d)
       && $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h)
     ==> $IsAlloc(_module.DList.nodes(d), TSeq(Tclass._module.Node(_module.DList$A)), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.DList.freeStack(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.DList.DList_q(d)
       && (exists _module.DList$A: Ty :: 
        { $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h) } 
        $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h))
     ==> $IsAlloc(_module.DList.freeStack(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.DList$A: Ty, $h: Heap :: 
  { $IsAlloc(_module.DList.s(d), TSeq(_module.DList$A), $h) } 
  $IsGoodHeap($h)
       && 
      _module.DList.DList_q(d)
       && $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h)
     ==> $IsAlloc(_module.DList.s(d), TSeq(_module.DList$A), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.DList.f(d), TSeq(TInt), $h) } 
  $IsGoodHeap($h)
       && 
      _module.DList.DList_q(d)
       && (exists _module.DList$A: Ty :: 
        { $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h) } 
        $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h))
     ==> $IsAlloc(_module.DList.f(d), TSeq(TInt), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.DList.g(d), TSeq(TInt), $h) } 
  $IsGoodHeap($h)
       && 
      _module.DList.DList_q(d)
       && (exists _module.DList$A: Ty :: 
        { $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h) } 
        $IsAlloc(d, Tclass._module.DList(_module.DList$A), $h))
     ==> $IsAlloc(_module.DList.g(d), TSeq(TInt), $h));

// Constructor literal
axiom (forall a#39#0#0: Seq Box, 
    a#39#1#0: int, 
    a#39#2#0: Seq Box, 
    a#39#3#0: Seq Box, 
    a#39#4#0: Seq Box :: 
  { #_module.DList.DList(Lit(a#39#0#0), LitInt(a#39#1#0), Lit(a#39#2#0), Lit(a#39#3#0), Lit(a#39#4#0)) } 
  #_module.DList.DList(Lit(a#39#0#0), LitInt(a#39#1#0), Lit(a#39#2#0), Lit(a#39#3#0), Lit(a#39#4#0))
     == Lit(#_module.DList.DList(a#39#0#0, a#39#1#0, a#39#2#0, a#39#3#0, a#39#4#0)));

function _module.DList.nodes(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#40#0#0: Seq Box, 
    a#40#1#0: int, 
    a#40#2#0: Seq Box, 
    a#40#3#0: Seq Box, 
    a#40#4#0: Seq Box :: 
  { #_module.DList.DList(a#40#0#0, a#40#1#0, a#40#2#0, a#40#3#0, a#40#4#0) } 
  _module.DList.nodes(#_module.DList.DList(a#40#0#0, a#40#1#0, a#40#2#0, a#40#3#0, a#40#4#0))
     == a#40#0#0);

// Inductive seq element rank
axiom (forall a#41#0#0: Seq Box, 
    a#41#1#0: int, 
    a#41#2#0: Seq Box, 
    a#41#3#0: Seq Box, 
    a#41#4#0: Seq Box, 
    i: int :: 
  { Seq#Index(a#41#0#0, i), #_module.DList.DList(a#41#0#0, a#41#1#0, a#41#2#0, a#41#3#0, a#41#4#0) } 
  0 <= i && i < Seq#Length(a#41#0#0)
     ==> DtRank($Unbox(Seq#Index(a#41#0#0, i)): DatatypeType)
       < DtRank(#_module.DList.DList(a#41#0#0, a#41#1#0, a#41#2#0, a#41#3#0, a#41#4#0)));

// Inductive seq rank
axiom (forall a#42#0#0: Seq Box, 
    a#42#1#0: int, 
    a#42#2#0: Seq Box, 
    a#42#3#0: Seq Box, 
    a#42#4#0: Seq Box :: 
  { #_module.DList.DList(a#42#0#0, a#42#1#0, a#42#2#0, a#42#3#0, a#42#4#0) } 
  Seq#Rank(a#42#0#0)
     < DtRank(#_module.DList.DList(a#42#0#0, a#42#1#0, a#42#2#0, a#42#3#0, a#42#4#0)));

function _module.DList.freeStack(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#43#0#0: Seq Box, 
    a#43#1#0: int, 
    a#43#2#0: Seq Box, 
    a#43#3#0: Seq Box, 
    a#43#4#0: Seq Box :: 
  { #_module.DList.DList(a#43#0#0, a#43#1#0, a#43#2#0, a#43#3#0, a#43#4#0) } 
  _module.DList.freeStack(#_module.DList.DList(a#43#0#0, a#43#1#0, a#43#2#0, a#43#3#0, a#43#4#0))
     == a#43#1#0);

function _module.DList.s(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#44#0#0: Seq Box, 
    a#44#1#0: int, 
    a#44#2#0: Seq Box, 
    a#44#3#0: Seq Box, 
    a#44#4#0: Seq Box :: 
  { #_module.DList.DList(a#44#0#0, a#44#1#0, a#44#2#0, a#44#3#0, a#44#4#0) } 
  _module.DList.s(#_module.DList.DList(a#44#0#0, a#44#1#0, a#44#2#0, a#44#3#0, a#44#4#0))
     == a#44#2#0);

// Inductive seq element rank
axiom (forall a#45#0#0: Seq Box, 
    a#45#1#0: int, 
    a#45#2#0: Seq Box, 
    a#45#3#0: Seq Box, 
    a#45#4#0: Seq Box, 
    i: int :: 
  { Seq#Index(a#45#2#0, i), #_module.DList.DList(a#45#0#0, a#45#1#0, a#45#2#0, a#45#3#0, a#45#4#0) } 
  0 <= i && i < Seq#Length(a#45#2#0)
     ==> DtRank($Unbox(Seq#Index(a#45#2#0, i)): DatatypeType)
       < DtRank(#_module.DList.DList(a#45#0#0, a#45#1#0, a#45#2#0, a#45#3#0, a#45#4#0)));

// Inductive seq rank
axiom (forall a#46#0#0: Seq Box, 
    a#46#1#0: int, 
    a#46#2#0: Seq Box, 
    a#46#3#0: Seq Box, 
    a#46#4#0: Seq Box :: 
  { #_module.DList.DList(a#46#0#0, a#46#1#0, a#46#2#0, a#46#3#0, a#46#4#0) } 
  Seq#Rank(a#46#2#0)
     < DtRank(#_module.DList.DList(a#46#0#0, a#46#1#0, a#46#2#0, a#46#3#0, a#46#4#0)));

function _module.DList.f(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#47#0#0: Seq Box, 
    a#47#1#0: int, 
    a#47#2#0: Seq Box, 
    a#47#3#0: Seq Box, 
    a#47#4#0: Seq Box :: 
  { #_module.DList.DList(a#47#0#0, a#47#1#0, a#47#2#0, a#47#3#0, a#47#4#0) } 
  _module.DList.f(#_module.DList.DList(a#47#0#0, a#47#1#0, a#47#2#0, a#47#3#0, a#47#4#0))
     == a#47#3#0);

// Inductive seq element rank
axiom (forall a#48#0#0: Seq Box, 
    a#48#1#0: int, 
    a#48#2#0: Seq Box, 
    a#48#3#0: Seq Box, 
    a#48#4#0: Seq Box, 
    i: int :: 
  { Seq#Index(a#48#3#0, i), #_module.DList.DList(a#48#0#0, a#48#1#0, a#48#2#0, a#48#3#0, a#48#4#0) } 
  0 <= i && i < Seq#Length(a#48#3#0)
     ==> DtRank($Unbox(Seq#Index(a#48#3#0, i)): DatatypeType)
       < DtRank(#_module.DList.DList(a#48#0#0, a#48#1#0, a#48#2#0, a#48#3#0, a#48#4#0)));

// Inductive seq rank
axiom (forall a#49#0#0: Seq Box, 
    a#49#1#0: int, 
    a#49#2#0: Seq Box, 
    a#49#3#0: Seq Box, 
    a#49#4#0: Seq Box :: 
  { #_module.DList.DList(a#49#0#0, a#49#1#0, a#49#2#0, a#49#3#0, a#49#4#0) } 
  Seq#Rank(a#49#3#0)
     < DtRank(#_module.DList.DList(a#49#0#0, a#49#1#0, a#49#2#0, a#49#3#0, a#49#4#0)));

function _module.DList.g(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#50#0#0: Seq Box, 
    a#50#1#0: int, 
    a#50#2#0: Seq Box, 
    a#50#3#0: Seq Box, 
    a#50#4#0: Seq Box :: 
  { #_module.DList.DList(a#50#0#0, a#50#1#0, a#50#2#0, a#50#3#0, a#50#4#0) } 
  _module.DList.g(#_module.DList.DList(a#50#0#0, a#50#1#0, a#50#2#0, a#50#3#0, a#50#4#0))
     == a#50#4#0);

// Inductive seq element rank
axiom (forall a#51#0#0: Seq Box, 
    a#51#1#0: int, 
    a#51#2#0: Seq Box, 
    a#51#3#0: Seq Box, 
    a#51#4#0: Seq Box, 
    i: int :: 
  { Seq#Index(a#51#4#0, i), #_module.DList.DList(a#51#0#0, a#51#1#0, a#51#2#0, a#51#3#0, a#51#4#0) } 
  0 <= i && i < Seq#Length(a#51#4#0)
     ==> DtRank($Unbox(Seq#Index(a#51#4#0, i)): DatatypeType)
       < DtRank(#_module.DList.DList(a#51#0#0, a#51#1#0, a#51#2#0, a#51#3#0, a#51#4#0)));

// Inductive seq rank
axiom (forall a#52#0#0: Seq Box, 
    a#52#1#0: int, 
    a#52#2#0: Seq Box, 
    a#52#3#0: Seq Box, 
    a#52#4#0: Seq Box :: 
  { #_module.DList.DList(a#52#0#0, a#52#1#0, a#52#2#0, a#52#3#0, a#52#4#0) } 
  Seq#Rank(a#52#4#0)
     < DtRank(#_module.DList.DList(a#52#0#0, a#52#1#0, a#52#2#0, a#52#3#0, a#52#4#0)));

// Depth-one case-split function
function $IsA#_module.DList(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.DList(d) } 
  $IsA#_module.DList(d) ==> _module.DList.DList_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.DList$A: Ty, d: DatatypeType :: 
  { _module.DList.DList_q(d), $Is(d, Tclass._module.DList(_module.DList$A)) } 
  $Is(d, Tclass._module.DList(_module.DList$A)) ==> _module.DList.DList_q(d));

// Datatype extensional equality declaration
function _module.DList#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.DList.DList
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DList#Equal(a, b) } 
  true
     ==> (_module.DList#Equal(a, b)
       <==> Seq#Equal(_module.DList.nodes(a), _module.DList.nodes(b))
         && _module.DList.freeStack(a) == _module.DList.freeStack(b)
         && Seq#Equal(_module.DList.s(a), _module.DList.s(b))
         && Seq#Equal(_module.DList.f(a), _module.DList.f(b))
         && Seq#Equal(_module.DList.g(a), _module.DList.g(b))));

// Datatype extensionality axiom: _module.DList
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DList#Equal(a, b) } 
  _module.DList#Equal(a, b) <==> a == b);

const unique class._module.DList: ClassName;

const unique class._module.__default: ClassName;

function Tclass._module.__default() : Ty;

// Tclass._module.__default Tag
axiom Tag(Tclass._module.__default()) == Tagclass._module.__default;

const unique Tagclass._module.__default: TyTag;

// Box/unbox axiom for Tclass._module.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.__default()) } 
  $IsBox(bx, Tclass._module.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.__default()) } 
  $Is($o, Tclass._module.__default())
     <==> $o == null || dtype($o) == Tclass._module.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.__default(), $h) } 
  $IsAlloc($o, Tclass._module.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module._default.Dec
function _module.__default.Dec(a#0: int, b#0: int) : int;

function _module.__default.Dec#canCall(a#0: int, b#0: int) : bool;

// consequence axiom for _module.__default.Dec
axiom 23 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int :: 
    { _module.__default.Dec(a#0, b#0) } 
    _module.__default.Dec#canCall(a#0, b#0) || 23 != $FunctionContextHeight ==> true);

function _module.__default.Dec#requires(int, int) : bool;

// #requires axiom for _module.__default.Dec
axiom (forall a#0: int, b#0: int :: 
  { _module.__default.Dec#requires(a#0, b#0) } 
  _module.__default.Dec#requires(a#0, b#0) == true);

procedure CheckWellformed$$_module.__default.Dec(a#0: int, b#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.Props__dec__one(sum#0: int);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Props__dec__one(sum#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall j#1: int, _t#0#0: int :: 
    { _module.__default.Dec(sum#0, j#1), _module.__default.Dec(sum#0, _t#0#0) } 
    _t#0#0 == j#1 + 1
       ==> _module.__default.Dec#canCall(sum#0, _t#0#0)
         && _module.__default.Dec#canCall(sum#0, j#1));
  ensures (forall j#1: int, _t#0#0: int :: 
    { _module.__default.Dec(sum#0, j#1), _module.__default.Dec(sum#0, _t#0#0) } 
    _t#0#0 == j#1 + 1
       ==> _module.__default.Dec(sum#0, _t#0#0) < _module.__default.Dec(sum#0, j#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure CheckWellformed$$_module.__default.Props__dec__lower__bound(sum#0: int, x#0: int);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Props__dec__lower__bound(sum#0: int, x#0: int);
  // user-defined preconditions
  requires x#0 <= sum#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Dec#canCall(sum#0, x#0);
  ensures LitInt(0) <= _module.__default.Dec(sum#0, x#0);
  // frame condition
  free ensures old($Heap) == $Heap;



// function declaration for _module._default.Add
function _module.__default.Add(a#0: int, b#0: int) : int;

function _module.__default.Add#canCall(a#0: int, b#0: int) : bool;

// consequence axiom for _module.__default.Add
axiom 9 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int :: 
    { _module.__default.Add(a#0, b#0) } 
    _module.__default.Add#canCall(a#0, b#0) || 9 != $FunctionContextHeight ==> true);

function _module.__default.Add#requires(int, int) : bool;

// #requires axiom for _module.__default.Add
axiom (forall a#0: int, b#0: int :: 
  { _module.__default.Add#requires(a#0, b#0) } 
  _module.__default.Add#requires(a#0, b#0) == true);

// definition axiom for _module.__default.Add (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int :: 
    { _module.__default.Add(a#0, b#0) } 
    _module.__default.Add#canCall(a#0, b#0) || 9 != $FunctionContextHeight
       ==> _module.__default.Add(a#0, b#0) == a#0 + b#0);

// definition axiom for _module.__default.Add for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int :: 
    {:weight 3} { _module.__default.Add(LitInt(a#0), LitInt(b#0)) } 
    _module.__default.Add#canCall(LitInt(a#0), LitInt(b#0))
         || 9 != $FunctionContextHeight
       ==> _module.__default.Add(LitInt(a#0), LitInt(b#0)) == LitInt(a#0 + b#0));

procedure CheckWellformed$$_module.__default.Add(a#0: int, b#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.Sub
function _module.__default.Sub(a#0: int, b#0: int) : int;

function _module.__default.Sub#canCall(a#0: int, b#0: int) : bool;

// consequence axiom for _module.__default.Sub
axiom 10 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int :: 
    { _module.__default.Sub(a#0, b#0) } 
    _module.__default.Sub#canCall(a#0, b#0) || 10 != $FunctionContextHeight ==> true);

function _module.__default.Sub#requires(int, int) : bool;

// #requires axiom for _module.__default.Sub
axiom (forall a#0: int, b#0: int :: 
  { _module.__default.Sub#requires(a#0, b#0) } 
  _module.__default.Sub#requires(a#0, b#0) == true);

// definition axiom for _module.__default.Sub (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int :: 
    { _module.__default.Sub(a#0, b#0) } 
    _module.__default.Sub#canCall(a#0, b#0) || 10 != $FunctionContextHeight
       ==> _module.__default.Sub(a#0, b#0) == a#0 - b#0);

// definition axiom for _module.__default.Sub for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall a#0: int, b#0: int :: 
    {:weight 3} { _module.__default.Sub(LitInt(a#0), LitInt(b#0)) } 
    _module.__default.Sub#canCall(LitInt(a#0), LitInt(b#0))
         || 10 != $FunctionContextHeight
       ==> _module.__default.Sub(LitInt(a#0), LitInt(b#0)) == LitInt(a#0 - b#0));

procedure CheckWellformed$$_module.__default.Sub(a#0: int, b#0: int);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.SeqRemove
function _module.__default.SeqRemove(_module._default.SeqRemove$X: Ty, s#0: Seq Box, k#0: int) : Seq Box;

function _module.__default.SeqRemove#canCall(_module._default.SeqRemove$X: Ty, s#0: Seq Box, k#0: int) : bool;

// consequence axiom for _module.__default.SeqRemove
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.SeqRemove$X: Ty, s#0: Seq Box, k#0: int :: 
    { _module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0) } 
    _module.__default.SeqRemove#canCall(_module._default.SeqRemove$X, s#0, k#0)
         || (33 != $FunctionContextHeight
           && 
          $Is(s#0, TSeq(_module._default.SeqRemove$X))
           && 
          LitInt(0) <= k#0
           && k#0 < Seq#Length(s#0))
       ==> _module.__default.Sub(Seq#Length(s#0), LitInt(1))
           == Seq#Length(_module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0))
         && (forall i#0: int :: 
          { Seq#Index(_module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0), i#0) } 
          true
             ==> 
            LitInt(0) <= i#0
               && i#0
                 < Seq#Length(_module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0))
             ==> (if i#0 < k#0
               then Seq#Index(_module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0), i#0)
                 == Seq#Index(s#0, i#0)
               else Seq#Index(_module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0), i#0)
                 == Seq#Index(s#0, _module.__default.Add(i#0, LitInt(1)))))
         && $Is(_module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0), 
          TSeq(_module._default.SeqRemove$X)));

function _module.__default.SeqRemove#requires(Ty, Seq Box, int) : bool;

// #requires axiom for _module.__default.SeqRemove
axiom (forall _module._default.SeqRemove$X: Ty, s#0: Seq Box, k#0: int :: 
  { _module.__default.SeqRemove#requires(_module._default.SeqRemove$X, s#0, k#0) } 
  $Is(s#0, TSeq(_module._default.SeqRemove$X))
     ==> _module.__default.SeqRemove#requires(_module._default.SeqRemove$X, s#0, k#0)
       == (LitInt(0) <= k#0 && k#0 < Seq#Length(s#0)));

procedure CheckWellformed$$_module.__default.SeqRemove(_module._default.SeqRemove$X: Ty, 
    s#0: Seq Box where $Is(s#0, TSeq(_module._default.SeqRemove$X)), 
    k#0: int)
   returns (s'#0: Seq Box where $Is(s'#0, TSeq(_module._default.SeqRemove$X)));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.Sub(Seq#Length(s#0), LitInt(1)) == Seq#Length(s'#0);
  ensures (forall i#1: int :: 
    { Seq#Index(s'#0, i#1) } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < Seq#Length(s'#0)
       ==> (if i#1 < k#0
         then Seq#Index(s'#0, i#1) == Seq#Index(s#0, i#1)
         else Seq#Index(s'#0, i#1) == Seq#Index(s#0, _module.__default.Add(i#1, LitInt(1)))));



implementation CheckWellformed$$_module.__default.SeqRemove(_module._default.SeqRemove$X: Ty, s#0: Seq Box, k#0: int)
   returns (s'#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;
  var i#2: int;
  var ##a#1: int;
  var ##b#1: int;


    // AddWellformednessCheck for function SeqRemove
    assume {:captureState "DLL_Dafny.dfy(11,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (LitInt(0) <= k#0)
    {
    }

    assume LitInt(0) <= k#0 && k#0 < Seq#Length(s#0);
    if (*)
    {
        assume $Is(_module.__default.SeqRemove(_module._default.SeqRemove$X, s#0, k#0), 
          TSeq(_module._default.SeqRemove$X));
        ##a#0 := Seq#Length(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, TInt, $Heap);
        ##b#0 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, TInt, $Heap);
        assume _module.__default.Sub#canCall(Seq#Length(s#0), LitInt(1));
        assume _module.__default.Sub(Seq#Length(s#0), LitInt(1)) == Seq#Length(s'#0);
        havoc i#2;
        if (*)
        {
            assume LitInt(0) <= i#2;
            assume i#2 < Seq#Length(s'#0);
            if (*)
            {
                assume i#2 < k#0;
                assert 0 <= i#2 && i#2 < Seq#Length(s'#0);
                assert 0 <= i#2 && i#2 < Seq#Length(s#0);
                assume Seq#Index(s'#0, i#2) == Seq#Index(s#0, i#2);
            }
            else
            {
                assume k#0 <= i#2;
                assert 0 <= i#2 && i#2 < Seq#Length(s'#0);
                ##a#1 := i#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#1, TInt, $Heap);
                ##b#1 := LitInt(1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#1, TInt, $Heap);
                assume _module.__default.Add#canCall(i#2, LitInt(1));
                assert 0 <= _module.__default.Add(i#2, LitInt(1))
                   && _module.__default.Add(i#2, LitInt(1)) < Seq#Length(s#0);
                assume Seq#Index(s'#0, i#2) == Seq#Index(s#0, _module.__default.Add(i#2, LitInt(1)));
            }
        }
        else
        {
            assume LitInt(0) <= i#2 && i#2 < Seq#Length(s'#0)
               ==> (if i#2 < k#0
                 then Seq#Index(s'#0, i#2) == Seq#Index(s#0, i#2)
                 else Seq#Index(s'#0, i#2) == Seq#Index(s#0, _module.__default.Add(i#2, LitInt(1))));
        }

        assume (forall i#1: int :: 
          { Seq#Index(s'#0, i#1) } 
          true
             ==> 
            LitInt(0) <= i#1 && i#1 < Seq#Length(s'#0)
             ==> (if i#1 < k#0
               then Seq#Index(s'#0, i#1) == Seq#Index(s#0, i#1)
               else Seq#Index(s'#0, i#1) == Seq#Index(s#0, _module.__default.Add(i#1, LitInt(1)))));
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.SeqInsert
function _module.__default.SeqInsert(_module._default.SeqInsert$X: Ty, s#0: Seq Box, k#0: int, v#0: Box) : Seq Box;

function _module.__default.SeqInsert#canCall(_module._default.SeqInsert$X: Ty, s#0: Seq Box, k#0: int, v#0: Box) : bool;

// consequence axiom for _module.__default.SeqInsert
axiom 36 <= $FunctionContextHeight
   ==> (forall _module._default.SeqInsert$X: Ty, s#0: Seq Box, k#0: int, v#0: Box :: 
    { _module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0) } 
    _module.__default.SeqInsert#canCall(_module._default.SeqInsert$X, s#0, k#0, v#0)
         || (36 != $FunctionContextHeight
           && 
          $Is(s#0, TSeq(_module._default.SeqInsert$X))
           && $IsBox(v#0, _module._default.SeqInsert$X)
           && 
          LitInt(0) <= k#0
           && k#0 <= Seq#Length(s#0))
       ==> Seq#Length(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0))
           == _module.__default.Add(Seq#Length(s#0), LitInt(1))
         && (forall i#0: int :: 
          { Seq#Index(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0), i#0) } 
          true
             ==> 
            LitInt(0) <= i#0
               && i#0
                 < Seq#Length(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0))
             ==> (if i#0 < k#0
               then Seq#Index(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0), i#0)
                 == Seq#Index(s#0, i#0)
               else (if i#0 == k#0
                 then Seq#Index(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0), i#0)
                   == v#0
                 else Seq#Index(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0), i#0)
                   == Seq#Index(s#0, _module.__default.Sub(i#0, LitInt(1))))))
         && $Is(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0), 
          TSeq(_module._default.SeqInsert$X)));

function _module.__default.SeqInsert#requires(Ty, Seq Box, int, Box) : bool;

// #requires axiom for _module.__default.SeqInsert
axiom (forall _module._default.SeqInsert$X: Ty, s#0: Seq Box, k#0: int, v#0: Box :: 
  { _module.__default.SeqInsert#requires(_module._default.SeqInsert$X, s#0, k#0, v#0) } 
  $Is(s#0, TSeq(_module._default.SeqInsert$X))
       && $IsBox(v#0, _module._default.SeqInsert$X)
     ==> _module.__default.SeqInsert#requires(_module._default.SeqInsert$X, s#0, k#0, v#0)
       == (LitInt(0) <= k#0 && k#0 <= Seq#Length(s#0)));

procedure CheckWellformed$$_module.__default.SeqInsert(_module._default.SeqInsert$X: Ty, 
    s#0: Seq Box where $Is(s#0, TSeq(_module._default.SeqInsert$X)), 
    k#0: int, 
    v#0: Box where $IsBox(v#0, _module._default.SeqInsert$X))
   returns (s'#0: Seq Box where $Is(s'#0, TSeq(_module._default.SeqInsert$X)));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures Seq#Length(s'#0) == _module.__default.Add(Seq#Length(s#0), LitInt(1));
  ensures (forall i#1: int :: 
    { Seq#Index(s'#0, i#1) } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < Seq#Length(s'#0)
       ==> (if i#1 < k#0
         then Seq#Index(s'#0, i#1) == Seq#Index(s#0, i#1)
         else (if i#1 == k#0
           then Seq#Index(s'#0, i#1) == v#0
           else Seq#Index(s'#0, i#1) == Seq#Index(s#0, _module.__default.Sub(i#1, LitInt(1))))));



implementation CheckWellformed$$_module.__default.SeqInsert(_module._default.SeqInsert$X: Ty, s#0: Seq Box, k#0: int, v#0: Box)
   returns (s'#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: int;
  var ##b#0: int;
  var i#2: int;
  var ##a#1: int;
  var ##b#1: int;


    // AddWellformednessCheck for function SeqInsert
    assume {:captureState "DLL_Dafny.dfy(18,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (LitInt(0) <= k#0)
    {
    }

    assume LitInt(0) <= k#0 && k#0 <= Seq#Length(s#0);
    if (*)
    {
        assume $Is(_module.__default.SeqInsert(_module._default.SeqInsert$X, s#0, k#0, v#0), 
          TSeq(_module._default.SeqInsert$X));
        ##a#0 := Seq#Length(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, TInt, $Heap);
        ##b#0 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, TInt, $Heap);
        assume _module.__default.Add#canCall(Seq#Length(s#0), LitInt(1));
        assume Seq#Length(s'#0) == _module.__default.Add(Seq#Length(s#0), LitInt(1));
        havoc i#2;
        if (*)
        {
            assume LitInt(0) <= i#2;
            assume i#2 < Seq#Length(s'#0);
            if (*)
            {
                assume i#2 < k#0;
                assert 0 <= i#2 && i#2 < Seq#Length(s'#0);
                assert 0 <= i#2 && i#2 < Seq#Length(s#0);
                assume Seq#Index(s'#0, i#2) == Seq#Index(s#0, i#2);
            }
            else
            {
                assume k#0 <= i#2;
                if (*)
                {
                    assume i#2 == k#0;
                    assert 0 <= i#2 && i#2 < Seq#Length(s'#0);
                    assume Seq#Index(s'#0, i#2) == v#0;
                }
                else
                {
                    assume i#2 != k#0;
                    assert 0 <= i#2 && i#2 < Seq#Length(s'#0);
                    ##a#1 := i#2;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##a#1, TInt, $Heap);
                    ##b#1 := LitInt(1);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##b#1, TInt, $Heap);
                    assume _module.__default.Sub#canCall(i#2, LitInt(1));
                    assert 0 <= _module.__default.Sub(i#2, LitInt(1))
                       && _module.__default.Sub(i#2, LitInt(1)) < Seq#Length(s#0);
                    assume Seq#Index(s'#0, i#2) == Seq#Index(s#0, _module.__default.Sub(i#2, LitInt(1)));
                }
            }
        }
        else
        {
            assume LitInt(0) <= i#2 && i#2 < Seq#Length(s'#0)
               ==> (if i#2 < k#0
                 then Seq#Index(s'#0, i#2) == Seq#Index(s#0, i#2)
                 else (if i#2 == k#0
                   then Seq#Index(s'#0, i#2) == v#0
                   else Seq#Index(s'#0, i#2) == Seq#Index(s#0, _module.__default.Sub(i#2, LitInt(1)))));
        }

        assume (forall i#1: int :: 
          { Seq#Index(s'#0, i#1) } 
          true
             ==> 
            LitInt(0) <= i#1 && i#1 < Seq#Length(s'#0)
             ==> (if i#1 < k#0
               then Seq#Index(s'#0, i#1) == Seq#Index(s#0, i#1)
               else (if i#1 == k#0
                 then Seq#Index(s'#0, i#1) == v#0
                 else Seq#Index(s'#0, i#1) == Seq#Index(s#0, _module.__default.Sub(i#1, LitInt(1))))));
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.SeqInit
function _module.__default.SeqInit(_module._default.SeqInit$X: Ty, len#0: int, func#0: HandleType) : Seq Box;

function _module.__default.SeqInit#canCall(_module._default.SeqInit$X: Ty, len#0: int, func#0: HandleType) : bool;

// consequence axiom for _module.__default.SeqInit
axiom 4 <= $FunctionContextHeight
   ==> (forall _module._default.SeqInit$X: Ty, $Heap: Heap, len#0: int, func#0: HandleType :: 
    { _module.__default.SeqInit(_module._default.SeqInit$X, len#0, func#0), $IsGoodHeap($Heap) } 
    _module.__default.SeqInit#canCall(_module._default.SeqInit$X, len#0, func#0)
         || (4 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(func#0, Tclass._System.___hPartialFunc1(TInt, _module._default.SeqInit$X))
           && 
          len#0 >= LitInt(0)
           && (forall i#0: int :: 
            { Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#0)) } 
            true
               ==> 
              LitInt(0) <= i#0 && i#0 < len#0
               ==> Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#0))))
       ==> Seq#Length(_module.__default.SeqInit(_module._default.SeqInit$X, len#0, func#0))
           == len#0
         && (forall i#1: int :: 
          { Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#1)) } 
            { Seq#Index(_module.__default.SeqInit(_module._default.SeqInit$X, len#0, func#0), i#1) } 
          true
             ==> 
            LitInt(0) <= i#1 && i#1 < len#0
             ==> Seq#Index(_module.__default.SeqInit(_module._default.SeqInit$X, len#0, func#0), i#1)
               == Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#1)))
         && $Is(_module.__default.SeqInit(_module._default.SeqInit$X, len#0, func#0), 
          TSeq(_module._default.SeqInit$X)));

function _module.__default.SeqInit#requires(Ty, int, HandleType) : bool;

// #requires axiom for _module.__default.SeqInit
axiom (forall _module._default.SeqInit$X: Ty, $Heap: Heap, len#0: int, func#0: HandleType :: 
  { _module.__default.SeqInit#requires(_module._default.SeqInit$X, len#0, func#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(func#0, Tclass._System.___hPartialFunc1(TInt, _module._default.SeqInit$X))
     ==> _module.__default.SeqInit#requires(_module._default.SeqInit$X, len#0, func#0)
       == (len#0 >= LitInt(0)
         && (forall i#2: int :: 
          { Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#2)) } 
          true
             ==> 
            LitInt(0) <= i#2 && i#2 < len#0
             ==> Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#2)))));

procedure CheckWellformed$$_module.__default.SeqInit(_module._default.SeqInit$X: Ty, 
    len#0: int, 
    func#0: HandleType
       where $Is(func#0, Tclass._System.___hPartialFunc1(TInt, _module._default.SeqInit$X)))
   returns (s#0: Seq Box where $Is(s#0, TSeq(_module._default.SeqInit$X)));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures Seq#Length(s#0) == len#0;
  ensures (forall i#3: int :: 
    { Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#3)) } 
      { Seq#Index(s#0, i#3) } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < len#0
       ==> Seq#Index(s#0, i#3)
         == Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#3)));



implementation CheckWellformed$$_module.__default.SeqInit(_module._default.SeqInit$X: Ty, len#0: int, func#0: HandleType)
   returns (s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#4: int;
  var ##x0#0: int;
  var b$reqreads#0: bool;
  var i#6: int;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SeqInit
    assume {:captureState "DLL_Dafny.dfy(26,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume len#0 >= LitInt(0);
    havoc i#4;
    if (*)
    {
        assume LitInt(0) <= i#4;
        assume i#4 < len#0;
        ##x0#0 := i#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x0#0, TInt, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(##x0#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Requires1#canCall(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#4));
        assume Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#4));
    }
    else
    {
        assume LitInt(0) <= i#4 && i#4 < len#0
           ==> Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#4));
    }

    assume (forall i#5: int :: 
      { Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#5)) } 
      true
         ==> 
        LitInt(0) <= i#5 && i#5 < len#0
         ==> Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#5)));
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.SeqInit(_module._default.SeqInit$X, len#0, func#0), 
          TSeq(_module._default.SeqInit$X));
        assume Seq#Length(s#0) == len#0;
        havoc i#6;
        if (*)
        {
            assume LitInt(0) <= i#6;
            assume i#6 < len#0;
            assert 0 <= i#6 && i#6 < Seq#Length(s#0);
            assert Requires1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#6));
            assume Seq#Index(s#0, i#6)
               == Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#6));
        }
        else
        {
            assume LitInt(0) <= i#6 && i#6 < len#0
               ==> Seq#Index(s#0, i#6)
                 == Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#6));
        }

        assume (forall i#3: int :: 
          { Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#3)) } 
            { Seq#Index(s#0, i#3) } 
          true
             ==> 
            LitInt(0) <= i#3 && i#3 < len#0
             ==> Seq#Index(s#0, i#3)
               == Apply1(TInt, _module._default.SeqInit$X, $Heap, func#0, $Box(i#3)));
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.seq_get
function _module.__default.seq__get(_module._default.seq_get$A: Ty, s#0: Seq Box, i#0: int) : Box;

function _module.__default.seq__get#canCall(_module._default.seq_get$A: Ty, s#0: Seq Box, i#0: int) : bool;

// consequence axiom for _module.__default.seq__get
axiom 18 <= $FunctionContextHeight
   ==> (forall _module._default.seq_get$A: Ty, s#0: Seq Box, i#0: int :: 
    { _module.__default.seq__get(_module._default.seq_get$A, s#0, i#0) } 
    _module.__default.seq__get#canCall(_module._default.seq_get$A, s#0, i#0)
         || (18 != $FunctionContextHeight
           && 
          $Is(s#0, TSeq(_module._default.seq_get$A))
           && 
          LitInt(0) <= i#0
           && i#0 < Seq#Length(s#0))
       ==> _module.__default.seq__get(_module._default.seq_get$A, s#0, i#0)
           == Seq#Index(s#0, i#0)
         && $IsBox(_module.__default.seq__get(_module._default.seq_get$A, s#0, i#0), 
          _module._default.seq_get$A));

function _module.__default.seq__get#requires(Ty, Seq Box, int) : bool;

// #requires axiom for _module.__default.seq__get
axiom (forall _module._default.seq_get$A: Ty, s#0: Seq Box, i#0: int :: 
  { _module.__default.seq__get#requires(_module._default.seq_get$A, s#0, i#0) } 
  $Is(s#0, TSeq(_module._default.seq_get$A))
     ==> _module.__default.seq__get#requires(_module._default.seq_get$A, s#0, i#0)
       == (LitInt(0) <= i#0 && i#0 < Seq#Length(s#0)));

procedure CheckWellformed$$_module.__default.seq__get(_module._default.seq_get$A: Ty, 
    s#0: Seq Box where $Is(s#0, TSeq(_module._default.seq_get$A)), 
    i#0: int)
   returns (a#0: Box where $IsBox(a#0, _module._default.seq_get$A));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures a#0 == Seq#Index(s#0, i#0);



implementation CheckWellformed$$_module.__default.seq__get(_module._default.seq_get$A: Ty, s#0: Seq Box, i#0: int) returns (a#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function seq_get
    assume {:captureState "DLL_Dafny.dfy(34,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (LitInt(0) <= i#0)
    {
    }

    assume LitInt(0) <= i#0 && i#0 < Seq#Length(s#0);
    if (*)
    {
        assume $IsBox(_module.__default.seq__get(_module._default.seq_get$A, s#0, i#0), 
          _module._default.seq_get$A);
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume a#0 == Seq#Index(s#0, i#0);
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.seq_set
function _module.__default.seq__set(_module._default.seq_set$A: Ty, s1#0: Seq Box, i#0: int, a#0: Box) : Seq Box;

function _module.__default.seq__set#canCall(_module._default.seq_set$A: Ty, s1#0: Seq Box, i#0: int, a#0: Box) : bool;

// consequence axiom for _module.__default.seq__set
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.seq_set$A: Ty, s1#0: Seq Box, i#0: int, a#0: Box :: 
    { _module.__default.seq__set(_module._default.seq_set$A, s1#0, i#0, a#0) } 
    _module.__default.seq__set#canCall(_module._default.seq_set$A, s1#0, i#0, a#0)
         || (24 != $FunctionContextHeight
           && 
          $Is(s1#0, TSeq(_module._default.seq_set$A))
           && $IsBox(a#0, _module._default.seq_set$A)
           && 
          LitInt(0) <= i#0
           && i#0 < Seq#Length(s1#0))
       ==> Seq#Equal(_module.__default.seq__set(_module._default.seq_set$A, s1#0, i#0, a#0), 
          Seq#Update(s1#0, i#0, a#0))
         && $Is(_module.__default.seq__set(_module._default.seq_set$A, s1#0, i#0, a#0), 
          TSeq(_module._default.seq_set$A)));

function _module.__default.seq__set#requires(Ty, Seq Box, int, Box) : bool;

// #requires axiom for _module.__default.seq__set
axiom (forall _module._default.seq_set$A: Ty, s1#0: Seq Box, i#0: int, a#0: Box :: 
  { _module.__default.seq__set#requires(_module._default.seq_set$A, s1#0, i#0, a#0) } 
  $Is(s1#0, TSeq(_module._default.seq_set$A))
       && $IsBox(a#0, _module._default.seq_set$A)
     ==> _module.__default.seq__set#requires(_module._default.seq_set$A, s1#0, i#0, a#0)
       == (LitInt(0) <= i#0 && i#0 < Seq#Length(s1#0)));

procedure CheckWellformed$$_module.__default.seq__set(_module._default.seq_set$A: Ty, 
    s1#0: Seq Box where $Is(s1#0, TSeq(_module._default.seq_set$A)), 
    i#0: int, 
    a#0: Box where $IsBox(a#0, _module._default.seq_set$A))
   returns (s2#0: Seq Box where $Is(s2#0, TSeq(_module._default.seq_set$A)));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures Seq#Equal(s2#0, Seq#Update(s1#0, i#0, a#0));



implementation CheckWellformed$$_module.__default.seq__set(_module._default.seq_set$A: Ty, s1#0: Seq Box, i#0: int, a#0: Box)
   returns (s2#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function seq_set
    assume {:captureState "DLL_Dafny.dfy(38,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (LitInt(0) <= i#0)
    {
    }

    assume LitInt(0) <= i#0 && i#0 < Seq#Length(s1#0);
    if (*)
    {
        assume $Is(_module.__default.seq__set(_module._default.seq_set$A, s1#0, i#0, a#0), 
          TSeq(_module._default.seq_set$A));
        assert 0 <= i#0 && i#0 < Seq#Length(s1#0);
        assume Seq#Equal(s2#0, Seq#Update(s1#0, i#0, a#0));
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.seq_length
function _module.__default.seq_length(_module._default.seq_length$A: Ty, s#0: Seq Box) : int;

function _module.__default.seq_length#canCall(_module._default.seq_length$A: Ty, s#0: Seq Box) : bool;

// consequence axiom for _module.__default.seq_length
axiom 22 <= $FunctionContextHeight
   ==> (forall _module._default.seq_length$A: Ty, s#0: Seq Box :: 
    { _module.__default.seq_length(_module._default.seq_length$A, s#0) } 
    _module.__default.seq_length#canCall(_module._default.seq_length$A, s#0)
         || (22 != $FunctionContextHeight && $Is(s#0, TSeq(_module._default.seq_length$A)))
       ==> _module.__default.seq_length(_module._default.seq_length$A, s#0)
         == Seq#Length(s#0));

function _module.__default.seq_length#requires(Ty, Seq Box) : bool;

// #requires axiom for _module.__default.seq_length
axiom (forall _module._default.seq_length$A: Ty, s#0: Seq Box :: 
  { _module.__default.seq_length#requires(_module._default.seq_length$A, s#0) } 
  $Is(s#0, TSeq(_module._default.seq_length$A))
     ==> _module.__default.seq_length#requires(_module._default.seq_length$A, s#0)
       == true);

procedure {:extern "LinearExtern", "seq_length"} CheckWellformed$$_module.__default.seq_length(_module._default.seq_length$A: Ty, 
    s#0: Seq Box where $Is(s#0, TSeq(_module._default.seq_length$A)))
   returns (n#0: int);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures n#0 == Seq#Length(s#0);



implementation {:extern "LinearExtern", "seq_length"} CheckWellformed$$_module.__default.seq_length(_module._default.seq_length$A: Ty, s#0: Seq Box) returns (n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function seq_length
    assume {:captureState "DLL_Dafny.dfy(42,55): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume n#0 == Seq#Length(s#0);
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.seq_empty
function _module.__default.seq_empty(_module._default.seq_empty$A: Ty) : Seq Box;

function _module.__default.seq_empty#canCall(_module._default.seq_empty$A: Ty) : bool;

// consequence axiom for _module.__default.seq_empty
axiom 44 <= $FunctionContextHeight
   ==> (forall _module._default.seq_empty$A: Ty :: 
    { _module.__default.seq_empty(_module._default.seq_empty$A) } 
    _module.__default.seq_empty#canCall(_module._default.seq_empty$A)
         || 44 != $FunctionContextHeight
       ==> Seq#Length(_module.__default.seq_empty(_module._default.seq_empty$A))
           == LitInt(0)
         && $Is(_module.__default.seq_empty(_module._default.seq_empty$A), 
          TSeq(_module._default.seq_empty$A)));

function _module.__default.seq_empty#requires(Ty) : bool;

// #requires axiom for _module.__default.seq_empty
axiom (forall _module._default.seq_empty$A: Ty :: 
  { _module.__default.seq_empty#requires(_module._default.seq_empty$A) } 
  _module.__default.seq_empty#requires(_module._default.seq_empty$A) == true);

procedure {:extern "LinearExtern", "seq_empty"} CheckWellformed$$_module.__default.seq_empty(_module._default.seq_empty$A: Ty)
   returns (s#0: Seq Box where $Is(s#0, TSeq(_module._default.seq_empty$A)));
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures Seq#Length(s#0) == LitInt(0);



implementation {:extern "LinearExtern", "seq_empty"} CheckWellformed$$_module.__default.seq_empty(_module._default.seq_empty$A: Ty) returns (s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function seq_empty
    assume {:captureState "DLL_Dafny.dfy(45,54): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.seq_empty(_module._default.seq_empty$A), 
          TSeq(_module._default.seq_empty$A));
        assume Seq#Length(s#0) == LitInt(0);
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.seq_alloc
function _module.__default.seq_alloc(_module._default.seq_alloc$A: Ty, length#0: int, a#0: Box) : Seq Box;

function _module.__default.seq_alloc#canCall(_module._default.seq_alloc$A: Ty, length#0: int, a#0: Box) : bool;

// consequence axiom for _module.__default.seq_alloc
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.seq_alloc$A: Ty, length#0: int, a#0: Box :: 
    { _module.__default.seq_alloc(_module._default.seq_alloc$A, length#0, a#0) } 
    _module.__default.seq_alloc#canCall(_module._default.seq_alloc$A, length#0, a#0)
         || (28 != $FunctionContextHeight && $IsBox(a#0, _module._default.seq_alloc$A))
       ==> Seq#Length(_module.__default.seq_alloc(_module._default.seq_alloc$A, length#0, a#0))
           == length#0
         && (forall i#0: int :: 
          { Seq#Index(_module.__default.seq_alloc(_module._default.seq_alloc$A, length#0, a#0), i#0) } 
          true
             ==> 
            LitInt(0) <= i#0
               && i#0
                 < Seq#Length(_module.__default.seq_alloc(_module._default.seq_alloc$A, length#0, a#0))
             ==> Seq#Index(_module.__default.seq_alloc(_module._default.seq_alloc$A, length#0, a#0), i#0)
               == a#0)
         && $Is(_module.__default.seq_alloc(_module._default.seq_alloc$A, length#0, a#0), 
          TSeq(_module._default.seq_alloc$A)));

function _module.__default.seq_alloc#requires(Ty, int, Box) : bool;

// #requires axiom for _module.__default.seq_alloc
axiom (forall _module._default.seq_alloc$A: Ty, length#0: int, a#0: Box :: 
  { _module.__default.seq_alloc#requires(_module._default.seq_alloc$A, length#0, a#0) } 
  $IsBox(a#0, _module._default.seq_alloc$A)
     ==> _module.__default.seq_alloc#requires(_module._default.seq_alloc$A, length#0, a#0)
       == true);

procedure {:extern "LinearExtern", "seq_alloc"} CheckWellformed$$_module.__default.seq_alloc(_module._default.seq_alloc$A: Ty, 
    length#0: int, 
    a#0: Box where $IsBox(a#0, _module._default.seq_alloc$A))
   returns (s#0: Seq Box where $Is(s#0, TSeq(_module._default.seq_alloc$A)));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures Seq#Length(s#0) == length#0;
  ensures (forall i#1: int :: 
    { Seq#Index(s#0, i#1) } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < Seq#Length(s#0)
       ==> Seq#Index(s#0, i#1) == a#0);



implementation {:extern "LinearExtern", "seq_alloc"} CheckWellformed$$_module.__default.seq_alloc(_module._default.seq_alloc$A: Ty, length#0: int, a#0: Box)
   returns (s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#2: int;


    // AddWellformednessCheck for function seq_alloc
    assume {:captureState "DLL_Dafny.dfy(48,54): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.seq_alloc(_module._default.seq_alloc$A, length#0, a#0), 
          TSeq(_module._default.seq_alloc$A));
        assume Seq#Length(s#0) == length#0;
        havoc i#2;
        if (*)
        {
            assume LitInt(0) <= i#2;
            assume i#2 < Seq#Length(s#0);
            assert 0 <= i#2 && i#2 < Seq#Length(s#0);
            assume Seq#Index(s#0, i#2) == a#0;
        }
        else
        {
            assume LitInt(0) <= i#2 && i#2 < Seq#Length(s#0) ==> Seq#Index(s#0, i#2) == a#0;
        }

        assume (forall i#1: int :: 
          { Seq#Index(s#0, i#1) } 
          true
             ==> 
            LitInt(0) <= i#1 && i#1 < Seq#Length(s#0)
             ==> Seq#Index(s#0, i#1) == a#0);
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.seq_free
function _module.__default.seq_free(_module._default.seq_free$A: Ty, s#0: Seq Box) : DatatypeType;

function _module.__default.seq_free#canCall(_module._default.seq_free$A: Ty, s#0: Seq Box) : bool;

// consequence axiom for _module.__default.seq_free
axiom 6 <= $FunctionContextHeight
   ==> (forall _module._default.seq_free$A: Ty, s#0: Seq Box :: 
    { _module.__default.seq_free(_module._default.seq_free$A, s#0) } 
    _module.__default.seq_free#canCall(_module._default.seq_free$A, s#0)
         || (6 != $FunctionContextHeight && $Is(s#0, TSeq(_module._default.seq_free$A)))
       ==> $Is(_module.__default.seq_free(_module._default.seq_free$A, s#0), 
        Tclass._System.Tuple0()));

function _module.__default.seq_free#requires(Ty, Seq Box) : bool;

// #requires axiom for _module.__default.seq_free
axiom (forall _module._default.seq_free$A: Ty, s#0: Seq Box :: 
  { _module.__default.seq_free#requires(_module._default.seq_free$A, s#0) } 
  $Is(s#0, TSeq(_module._default.seq_free$A))
     ==> _module.__default.seq_free#requires(_module._default.seq_free$A, s#0) == true);

procedure {:extern "LinearExtern", "seq_free"} CheckWellformed$$_module.__default.seq_free(_module._default.seq_free$A: Ty, 
    s#0: Seq Box where $Is(s#0, TSeq(_module._default.seq_free$A)));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.seq_unleash
function _module.__default.seq_unleash(_module._default.seq_unleash$A: Ty, s1#0: Seq Box) : Seq Box;

function _module.__default.seq_unleash#canCall(_module._default.seq_unleash$A: Ty, s1#0: Seq Box) : bool;

// consequence axiom for _module.__default.seq_unleash
axiom 45 <= $FunctionContextHeight
   ==> (forall _module._default.seq_unleash$A: Ty, s1#0: Seq Box :: 
    { _module.__default.seq_unleash(_module._default.seq_unleash$A, s1#0) } 
    _module.__default.seq_unleash#canCall(_module._default.seq_unleash$A, s1#0)
         || (45 != $FunctionContextHeight
           && $Is(s1#0, TSeq(_module._default.seq_unleash$A)))
       ==> Seq#Equal(s1#0, _module.__default.seq_unleash(_module._default.seq_unleash$A, s1#0))
         && $Is(_module.__default.seq_unleash(_module._default.seq_unleash$A, s1#0), 
          TSeq(_module._default.seq_unleash$A)));

function _module.__default.seq_unleash#requires(Ty, Seq Box) : bool;

// #requires axiom for _module.__default.seq_unleash
axiom (forall _module._default.seq_unleash$A: Ty, s1#0: Seq Box :: 
  { _module.__default.seq_unleash#requires(_module._default.seq_unleash$A, s1#0) } 
  $Is(s1#0, TSeq(_module._default.seq_unleash$A))
     ==> _module.__default.seq_unleash#requires(_module._default.seq_unleash$A, s1#0)
       == true);

procedure {:extern "LinearExtern", "seq_unleash"} CheckWellformed$$_module.__default.seq_unleash(_module._default.seq_unleash$A: Ty, 
    s1#0: Seq Box where $Is(s1#0, TSeq(_module._default.seq_unleash$A)))
   returns (s2#0: Seq Box where $Is(s2#0, TSeq(_module._default.seq_unleash$A)));
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures Seq#Equal(s1#0, s2#0);



implementation {:extern "LinearExtern", "seq_unleash"} CheckWellformed$$_module.__default.seq_unleash(_module._default.seq_unleash$A: Ty, s1#0: Seq Box) returns (s2#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function seq_unleash
    assume {:captureState "DLL_Dafny.dfy(54,56): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.seq_unleash(_module._default.seq_unleash$A, s1#0), 
          TSeq(_module._default.seq_unleash$A));
        assume Seq#Equal(s1#0, s2#0);
        assume false;
    }
    else
    {
        assume false;
    }
}



procedure CheckWellformed$$_module.__default.SeqResize(_module._default.SeqResize$A: Ty, 
    s#0: Seq Box
       where $Is(s#0, TSeq(_module._default.SeqResize$A))
         && $IsAlloc(s#0, TSeq(_module._default.SeqResize$A), $Heap), 
    newlen#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.SeqResize$A)
         && $IsAllocBox(a#0, _module._default.SeqResize$A, $Heap))
   returns (s2#0: Seq Box
       where $Is(s2#0, TSeq(_module._default.SeqResize$A))
         && $IsAlloc(s2#0, TSeq(_module._default.SeqResize$A), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SeqResize(_module._default.SeqResize$A: Ty, s#0: Seq Box, newlen#0: int, a#0: Box)
   returns (s2#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var j#0: int;

    // AddMethodImpl: SeqResize, CheckWellformed$$_module.__default.SeqResize
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(57,7): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc s2#0;
    assume {:captureState "DLL_Dafny.dfy(58,15): post-state"} true;
    assume Seq#Length(s2#0) == newlen#0;
    havoc j#0;
    if (*)
    {
        assume LitInt(0) <= j#0;
        assume j#0 < newlen#0;
        assert 0 <= j#0 && j#0 < Seq#Length(s2#0);
        if (j#0 < Seq#Length(s#0))
        {
            assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        }
        else
        {
        }

        assume Seq#Index(s2#0, j#0)
           == (if j#0 < Seq#Length(s#0) then Seq#Index(s#0, j#0) else a#0);
    }
    else
    {
        assume LitInt(0) <= j#0 && j#0 < newlen#0
           ==> Seq#Index(s2#0, j#0)
             == (if j#0 < Seq#Length(s#0) then Seq#Index(s#0, j#0) else a#0);
    }

    assume (forall j#1: int :: 
      { Seq#Index(s#0, j#1) } { Seq#Index(s2#0, j#1) } 
      true
         ==> 
        LitInt(0) <= j#1 && j#1 < newlen#0
         ==> Seq#Index(s2#0, j#1)
           == (if j#1 < Seq#Length(s#0) then Seq#Index(s#0, j#1) else a#0));
}



procedure Call$$_module.__default.SeqResize(_module._default.SeqResize$A: Ty, 
    s#0: Seq Box
       where $Is(s#0, TSeq(_module._default.SeqResize$A))
         && $IsAlloc(s#0, TSeq(_module._default.SeqResize$A), $Heap), 
    newlen#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.SeqResize$A)
         && $IsAllocBox(a#0, _module._default.SeqResize$A, $Heap))
   returns (s2#0: Seq Box
       where $Is(s2#0, TSeq(_module._default.SeqResize$A))
         && $IsAlloc(s2#0, TSeq(_module._default.SeqResize$A), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(s2#0) == newlen#0;
  free ensures true;
  ensures (forall j#1: int :: 
    { Seq#Index(s#0, j#1) } { Seq#Index(s2#0, j#1) } 
    true
       ==> 
      LitInt(0) <= j#1 && j#1 < newlen#0
       ==> Seq#Index(s2#0, j#1)
         == (if j#1 < Seq#Length(s#0) then Seq#Index(s#0, j#1) else a#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.AllocAndCopy(_module._default.AllocAndCopy$A: Ty, 
    source#0: Seq Box
       where $Is(source#0, TSeq(_module._default.AllocAndCopy$A))
         && $IsAlloc(source#0, TSeq(_module._default.AllocAndCopy$A), $Heap), 
    from#0: int, 
    to#0: int)
   returns (dest#0: Seq Box
       where $Is(dest#0, TSeq(_module._default.AllocAndCopy$A))
         && $IsAlloc(dest#0, TSeq(_module._default.AllocAndCopy$A), $Heap));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AllocAndCopy(_module._default.AllocAndCopy$A: Ty, source#0: Seq Box, from#0: int, to#0: int)
   returns (dest#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: AllocAndCopy, CheckWellformed$$_module.__default.AllocAndCopy
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(61,7): initial state"} true;
    if (LitInt(0) <= from#0)
    {
    }

    if (LitInt(0) <= from#0 && from#0 <= to#0)
    {
    }

    assume LitInt(0) <= from#0 && from#0 <= to#0 && to#0 <= Seq#Length(source#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc dest#0;
    assume {:captureState "DLL_Dafny.dfy(64,27): post-state"} true;
    assert 0 <= from#0 && from#0 <= Seq#Length(source#0);
    assert from#0 <= to#0 && to#0 <= Seq#Length(source#0);
    assume Seq#Equal(Seq#Drop(Seq#Take(source#0, to#0), from#0), dest#0);
}



procedure Call$$_module.__default.AllocAndCopy(_module._default.AllocAndCopy$A: Ty, 
    source#0: Seq Box
       where $Is(source#0, TSeq(_module._default.AllocAndCopy$A))
         && $IsAlloc(source#0, TSeq(_module._default.AllocAndCopy$A), $Heap), 
    from#0: int, 
    to#0: int)
   returns (dest#0: Seq Box
       where $Is(dest#0, TSeq(_module._default.AllocAndCopy$A))
         && $IsAlloc(dest#0, TSeq(_module._default.AllocAndCopy$A), $Heap));
  // user-defined preconditions
  requires LitInt(0) <= from#0;
  requires from#0 <= to#0;
  requires to#0 <= Seq#Length(source#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(Seq#Drop(Seq#Take(source#0, to#0), from#0), dest#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function {:inline} _module.__default.unused() : int
{
  LitInt(0 - 2)
}

procedure CheckWellformed$$_module.__default.unused();
  free requires 8 == $FunctionContextHeight;



// _default.unused: Type axiom
axiom 8 < $FunctionContextHeight ==> $Is(_module.__default.unused(), TInt);

// _default.unused: Allocation axiom
axiom 8 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.__default.unused(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.__default.unused(), TInt, $h));

function {:inline} _module.__default.sentinel() : int
{
  LitInt(0 - 1)
}

procedure CheckWellformed$$_module.__default.sentinel();
  free requires 7 == $FunctionContextHeight;



// _default.sentinel: Type axiom
axiom 7 < $FunctionContextHeight ==> $Is(_module.__default.sentinel(), TInt);

// _default.sentinel: Allocation axiom
axiom 7 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.__default.sentinel(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.__default.sentinel(), TInt, $h));

// function declaration for _module._default.Invs
function _module.__default.Invs(_module._default.Invs$A: Ty, 
    nodes#0: Seq Box, 
    freeStack#0: int, 
    s#0: Seq Box, 
    f#0: Seq Box, 
    g#0: Seq Box)
   : bool;

function _module.__default.Invs#canCall(_module._default.Invs$A: Ty, 
    nodes#0: Seq Box, 
    freeStack#0: int, 
    s#0: Seq Box, 
    f#0: Seq Box, 
    g#0: Seq Box)
   : bool;

// consequence axiom for _module.__default.Invs
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.Invs$A: Ty, 
      nodes#0: Seq Box, 
      freeStack#0: int, 
      s#0: Seq Box, 
      f#0: Seq Box, 
      g#0: Seq Box :: 
    { _module.__default.Invs(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0) } 
    _module.__default.Invs#canCall(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Invs$A)))
           && $Is(s#0, TSeq(_module._default.Invs$A))
           && $Is(f#0, TSeq(TInt))
           && $Is(g#0, TSeq(TInt)))
       ==> true);

function _module.__default.Invs#requires(Ty, Seq Box, int, Seq Box, Seq Box, Seq Box) : bool;

// #requires axiom for _module.__default.Invs
axiom (forall _module._default.Invs$A: Ty, 
    nodes#0: Seq Box, 
    freeStack#0: int, 
    s#0: Seq Box, 
    f#0: Seq Box, 
    g#0: Seq Box :: 
  { _module.__default.Invs#requires(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0) } 
  $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Invs$A)))
       && $Is(s#0, TSeq(_module._default.Invs$A))
       && $Is(f#0, TSeq(TInt))
       && $Is(g#0, TSeq(TInt))
     ==> _module.__default.Invs#requires(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0)
       == true);

// definition axiom for _module.__default.Invs (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.Invs$A: Ty, 
      nodes#0: Seq Box, 
      freeStack#0: int, 
      s#0: Seq Box, 
      f#0: Seq Box, 
      g#0: Seq Box :: 
    { _module.__default.Invs(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0) } 
    _module.__default.Invs#canCall(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Invs$A)))
           && $Is(s#0, TSeq(_module._default.Invs$A))
           && $Is(f#0, TSeq(TInt))
           && $Is(g#0, TSeq(TInt)))
       ==> (Seq#Length(f#0) == Seq#Length(s#0)
           ==> 
          Seq#Length(g#0) == Seq#Length(nodes#0)
           ==> 
          Seq#Length(nodes#0) > 0
           ==> 
          $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           ==> 
          LitInt(0) <= freeStack#0
           ==> 
          freeStack#0 < Seq#Length(nodes#0)
           ==> 
          (forall i#0: int :: 
            { $Unbox(Seq#Index(f#0, i#0)): int } 
            true
               ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#0)): int)
                 && (LitInt(0) <= i#0 && i#0 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#0)): int < Seq#Length(nodes#0)))
           ==> 
          (forall i#1: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#1)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#1 && i#1 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#1)): int)): int == i#1)
           ==> 
          (forall p#0: int :: 
            { $Unbox(Seq#Index(g#0, p#0)): int } 
            true
               ==> (LitInt(0) <= p#0 && p#0 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#0)): int)
                 && (LitInt(0) <= p#0 && p#0 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#0)): int < Seq#Length(s#0)))
           ==> (forall p#1: int :: 
              { $Unbox(Seq#Index(nodes#0, p#1)): DatatypeType } 
              (LitInt(0) <= p#1
                   ==> 
                  p#1 < Seq#Length(g#0)
                   ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#1)): DatatypeType))
                 && (
                  (LitInt(0) <= p#1 && p#1 < Seq#Length(g#0)
                   ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#1)): DatatypeType))
                   ==> 
                  LitInt(0) <= p#1
                   ==> 
                  p#1 < Seq#Length(g#0)
                   ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#1)): DatatypeType)))
             && ((forall p#1: int :: 
                { $Unbox(Seq#Index(nodes#0, p#1)): DatatypeType } 
                true
                   ==> (LitInt(0) <= p#1 && p#1 < Seq#Length(g#0)
                       ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#1)): DatatypeType))
                     && (LitInt(0) <= p#1 && p#1 < Seq#Length(g#0)
                       ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#1)): DatatypeType)
                         < Seq#Length(g#0)))
               ==> (forall p#2: int :: 
                  { $Unbox(Seq#Index(g#0, p#2)): int } 
                    { $Unbox(Seq#Index(nodes#0, p#2)): DatatypeType } 
                  LitInt(0) <= p#2
                     ==> 
                    p#2 < Seq#Length(g#0)
                     ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#2)): DatatypeType))
                 && ((forall p#2: int :: 
                    { $Unbox(Seq#Index(g#0, p#2)): int } 
                      { $Unbox(Seq#Index(nodes#0, p#2)): DatatypeType } 
                    true
                       ==> 
                      LitInt(0) <= p#2 && p#2 < Seq#Length(g#0)
                       ==> ($Unbox(Seq#Index(g#0, p#2)): int >= LitInt(0)
                         <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#2)): DatatypeType))))
                   ==> 
                  (forall p#3: int :: 
                    { $Unbox(Seq#Index(g#0, p#3)): int } 
                    true
                       ==> 
                      LitInt(0) <= p#3
                         && p#3 < Seq#Length(g#0)
                         && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#3)): int
                       ==> 
                      $Unbox(Seq#Index(g#0, p#3)): int == _module.__default.sentinel()
                       ==> p#3 == LitInt(0))
                   ==> (forall p#4: int :: 
                      { $Unbox(Seq#Index(g#0, p#4)): int } 
                        { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#4)): int)): int } 
                        { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#4)): int) } 
                      LitInt(0) <= p#4
                         ==> 
                        p#4 < Seq#Length(g#0)
                         ==> 
                        _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#4)): int
                         ==> 
                        LitInt(0) <= $Unbox(Seq#Index(g#0, p#4)): int
                         ==> 
                        $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#4)): int)): int == p#4
                         ==> $IsA#_module.Option(_module.Node.data($Unbox(Seq#Index(nodes#0, p#4)): DatatypeType))
                           && _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#4)): DatatypeType))
                     && ((forall p#4: int :: 
                        { $Unbox(Seq#Index(g#0, p#4)): int } 
                          { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#4)): int)): int } 
                          { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#4)): int) } 
                        true
                           ==> 
                          LitInt(0) <= p#4
                             && p#4 < Seq#Length(g#0)
                             && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#4)): int
                           ==> 
                          LitInt(0) <= $Unbox(Seq#Index(g#0, p#4)): int
                           ==> $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#4)): int)): int == p#4
                             && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(nodes#0, p#4)): DatatypeType), 
                              #_module.Option.Some(Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#4)): int))))
                       ==> (forall p#5: int :: 
                          { $Unbox(Seq#Index(g#0, p#5)): int } 
                            { _module.Node.next($Unbox(Seq#Index(nodes#0, p#5)): DatatypeType) } 
                          LitInt(0) <= p#5
                             ==> 
                            p#5 < Seq#Length(g#0)
                             ==> 
                            _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#5)): int
                             ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#5)): DatatypeType)
                               && 
                              _module.__default.Add#canCall($Unbox(Seq#Index(g#0, p#5)): int, LitInt(1))
                               && (_module.__default.Add($Unbox(Seq#Index(g#0, p#5)): int, LitInt(1))
                                   < Seq#Length(f#0)
                                 ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, p#5)): int, LitInt(1))))
                         && ((forall p#5: int :: 
                            { $Unbox(Seq#Index(g#0, p#5)): int } 
                              { _module.Node.next($Unbox(Seq#Index(nodes#0, p#5)): DatatypeType) } 
                            true
                               ==> 
                              LitInt(0) <= p#5
                                 && p#5 < Seq#Length(g#0)
                                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#5)): int
                               ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#5)): DatatypeType)
                                 == (if _module.__default.Add($Unbox(Seq#Index(g#0, p#5)): int, LitInt(1))
                                     < Seq#Length(f#0)
                                   then $Unbox(Seq#Index(f#0, _module.__default.Add($Unbox(Seq#Index(g#0, p#5)): int, LitInt(1)))): int
                                   else 0))
                           ==> (forall p#6: int :: 
                            { $Unbox(Seq#Index(g#0, p#6)): int } 
                              { _module.Node.prev($Unbox(Seq#Index(nodes#0, p#6)): DatatypeType) } 
                            (LitInt(0) <= p#6
                                 && p#6 < Seq#Length(g#0)
                                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#6)): int
                               ==> true)
                               ==> 
                              LitInt(0) <= p#6
                               ==> 
                              p#6 < Seq#Length(g#0)
                               ==> 
                              _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#6)): int
                               ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#6)): DatatypeType)
                                 && 
                                ($Unbox(Seq#Index(g#0, p#6)): int > 0
                                   ==> _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, p#6)): int, LitInt(1)))
                                 && (0 >= $Unbox(Seq#Index(g#0, p#6)): int
                                   ==> 
                                  !($Unbox(Seq#Index(g#0, p#6)): int == LitInt(0) || Seq#Length(f#0) == LitInt(0))
                                   ==> _module.__default.Sub#canCall(Seq#Length(f#0), LitInt(1)))))))))
         && _module.__default.Invs(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0)
           == (
            Seq#Length(f#0) == Seq#Length(s#0)
             && Seq#Length(g#0) == Seq#Length(nodes#0)
             && Seq#Length(nodes#0) > 0
             && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
             && 
            LitInt(0) <= freeStack#0
             && freeStack#0 < Seq#Length(nodes#0)
             && (forall i#0: int :: 
              { $Unbox(Seq#Index(f#0, i#0)): int } 
              true
                 ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(f#0)
                     ==> 0 < $Unbox(Seq#Index(f#0, i#0)): int)
                   && (LitInt(0) <= i#0 && i#0 < Seq#Length(f#0)
                     ==> $Unbox(Seq#Index(f#0, i#0)): int < Seq#Length(nodes#0)))
             && (forall i#1: int :: 
              { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#1)): int)): int } 
              true
                 ==> 
                LitInt(0) <= i#1 && i#1 < Seq#Length(f#0)
                 ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#1)): int)): int == i#1)
             && (forall p#0: int :: 
              { $Unbox(Seq#Index(g#0, p#0)): int } 
              true
                 ==> (LitInt(0) <= p#0 && p#0 < Seq#Length(g#0)
                     ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#0)): int)
                   && (LitInt(0) <= p#0 && p#0 < Seq#Length(g#0)
                     ==> $Unbox(Seq#Index(g#0, p#0)): int < Seq#Length(s#0)))
             && (forall p#1: int :: 
              { $Unbox(Seq#Index(nodes#0, p#1)): DatatypeType } 
              true
                 ==> (LitInt(0) <= p#1 && p#1 < Seq#Length(g#0)
                     ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#1)): DatatypeType))
                   && (LitInt(0) <= p#1 && p#1 < Seq#Length(g#0)
                     ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#1)): DatatypeType)
                       < Seq#Length(g#0)))
             && (forall p#2: int :: 
              { $Unbox(Seq#Index(g#0, p#2)): int } 
                { $Unbox(Seq#Index(nodes#0, p#2)): DatatypeType } 
              true
                 ==> 
                LitInt(0) <= p#2 && p#2 < Seq#Length(g#0)
                 ==> ($Unbox(Seq#Index(g#0, p#2)): int >= LitInt(0)
                   <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#2)): DatatypeType))))
             && (forall p#3: int :: 
              { $Unbox(Seq#Index(g#0, p#3)): int } 
              true
                 ==> 
                LitInt(0) <= p#3
                   && p#3 < Seq#Length(g#0)
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#3)): int
                 ==> 
                $Unbox(Seq#Index(g#0, p#3)): int == _module.__default.sentinel()
                 ==> p#3 == LitInt(0))
             && (forall p#4: int :: 
              { $Unbox(Seq#Index(g#0, p#4)): int } 
                { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#4)): int)): int } 
                { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#4)): int) } 
              true
                 ==> 
                LitInt(0) <= p#4
                   && p#4 < Seq#Length(g#0)
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#4)): int
                 ==> 
                LitInt(0) <= $Unbox(Seq#Index(g#0, p#4)): int
                 ==> $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#4)): int)): int == p#4
                   && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(nodes#0, p#4)): DatatypeType), 
                    #_module.Option.Some(Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#4)): int))))
             && (forall p#5: int :: 
              { $Unbox(Seq#Index(g#0, p#5)): int } 
                { _module.Node.next($Unbox(Seq#Index(nodes#0, p#5)): DatatypeType) } 
              true
                 ==> 
                LitInt(0) <= p#5
                   && p#5 < Seq#Length(g#0)
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#5)): int
                 ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#5)): DatatypeType)
                   == (if _module.__default.Add($Unbox(Seq#Index(g#0, p#5)): int, LitInt(1))
                       < Seq#Length(f#0)
                     then $Unbox(Seq#Index(f#0, _module.__default.Add($Unbox(Seq#Index(g#0, p#5)): int, LitInt(1)))): int
                     else 0))
             && (forall p#6: int :: 
              { $Unbox(Seq#Index(g#0, p#6)): int } 
                { _module.Node.prev($Unbox(Seq#Index(nodes#0, p#6)): DatatypeType) } 
              true
                 ==> (LitInt(0) <= p#6
                       && p#6 < Seq#Length(g#0)
                       && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#6)): int
                     ==> true)
                   && (LitInt(0) <= p#6
                       && p#6 < Seq#Length(g#0)
                       && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#6)): int
                     ==> _module.Node.prev($Unbox(Seq#Index(nodes#0, p#6)): DatatypeType)
                       == (if $Unbox(Seq#Index(g#0, p#6)): int > 0
                         then $Unbox(Seq#Index(f#0, _module.__default.Sub($Unbox(Seq#Index(g#0, p#6)): int, LitInt(1)))): int
                         else (if $Unbox(Seq#Index(g#0, p#6)): int == LitInt(0) || Seq#Length(f#0) == LitInt(0)
                           then 0
                           else $Unbox(Seq#Index(f#0, _module.__default.Sub(Seq#Length(f#0), LitInt(1)))): int))))));

// definition axiom for _module.__default.Invs for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.Invs$A: Ty, 
      nodes#0: Seq Box, 
      freeStack#0: int, 
      s#0: Seq Box, 
      f#0: Seq Box, 
      g#0: Seq Box :: 
    {:weight 3} { _module.__default.Invs(_module._default.Invs$A, 
        Lit(nodes#0), 
        LitInt(freeStack#0), 
        Lit(s#0), 
        Lit(f#0), 
        Lit(g#0)) } 
    _module.__default.Invs#canCall(_module._default.Invs$A, 
          Lit(nodes#0), 
          LitInt(freeStack#0), 
          Lit(s#0), 
          Lit(f#0), 
          Lit(g#0))
         || (11 != $FunctionContextHeight
           && 
          $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Invs$A)))
           && $Is(s#0, TSeq(_module._default.Invs$A))
           && $Is(f#0, TSeq(TInt))
           && $Is(g#0, TSeq(TInt)))
       ==> (Seq#Length(Lit(f#0)) == Seq#Length(Lit(s#0))
           ==> 
          Seq#Length(Lit(g#0)) == Seq#Length(Lit(nodes#0))
           ==> 
          Seq#Length(Lit(nodes#0)) > 0
           ==> 
          $Unbox(Seq#Index(Lit(g#0), LitInt(0))): int == _module.__default.sentinel()
           ==> 
          LitInt(0) <= LitInt(freeStack#0)
           ==> 
          freeStack#0 < Seq#Length(Lit(nodes#0))
           ==> 
          (forall i#2: int :: 
            { $Unbox(Seq#Index(f#0, i#2)): int } 
            true
               ==> (LitInt(0) <= i#2 && i#2 < Seq#Length(Lit(f#0))
                   ==> 0 < $Unbox(Seq#Index(Lit(f#0), i#2)): int)
                 && (LitInt(0) <= i#2 && i#2 < Seq#Length(Lit(f#0))
                   ==> $Unbox(Seq#Index(Lit(f#0), i#2)): int < Seq#Length(Lit(nodes#0))))
           ==> 
          (forall i#3: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#3)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#3 && i#3 < Seq#Length(Lit(f#0))
               ==> $Unbox(Seq#Index(Lit(g#0), $Unbox(Seq#Index(Lit(f#0), i#3)): int)): int == i#3)
           ==> 
          (forall p#7: int :: 
            { $Unbox(Seq#Index(g#0, p#7)): int } 
            true
               ==> (LitInt(0) <= p#7 && p#7 < Seq#Length(Lit(g#0))
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(Lit(g#0), p#7)): int)
                 && (LitInt(0) <= p#7 && p#7 < Seq#Length(Lit(g#0))
                   ==> $Unbox(Seq#Index(Lit(g#0), p#7)): int < Seq#Length(Lit(s#0))))
           ==> (forall p#8: int :: 
              { $Unbox(Seq#Index(nodes#0, p#8)): DatatypeType } 
              (LitInt(0) <= p#8
                   ==> 
                  p#8 < Seq#Length(Lit(g#0))
                   ==> _module.Node.Node_q($Unbox(Seq#Index(Lit(nodes#0), p#8)): DatatypeType))
                 && (
                  (LitInt(0) <= p#8 && p#8 < Seq#Length(Lit(g#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(Lit(nodes#0), p#8)): DatatypeType))
                   ==> 
                  LitInt(0) <= p#8
                   ==> 
                  p#8 < Seq#Length(Lit(g#0))
                   ==> _module.Node.Node_q($Unbox(Seq#Index(Lit(nodes#0), p#8)): DatatypeType)))
             && ((forall p#8: int :: 
                { $Unbox(Seq#Index(nodes#0, p#8)): DatatypeType } 
                true
                   ==> (LitInt(0) <= p#8 && p#8 < Seq#Length(Lit(g#0))
                       ==> LitInt(0)
                         <= _module.Node.next($Unbox(Seq#Index(Lit(nodes#0), p#8)): DatatypeType))
                     && (LitInt(0) <= p#8 && p#8 < Seq#Length(Lit(g#0))
                       ==> _module.Node.next($Unbox(Seq#Index(Lit(nodes#0), p#8)): DatatypeType)
                         < Seq#Length(Lit(g#0))))
               ==> (forall p#9: int :: 
                  { $Unbox(Seq#Index(g#0, p#9)): int } 
                    { $Unbox(Seq#Index(nodes#0, p#9)): DatatypeType } 
                  LitInt(0) <= p#9
                     ==> 
                    p#9 < Seq#Length(Lit(g#0))
                     ==> _module.Node.Node_q($Unbox(Seq#Index(Lit(nodes#0), p#9)): DatatypeType))
                 && ((forall p#9: int :: 
                    { $Unbox(Seq#Index(g#0, p#9)): int } 
                      { $Unbox(Seq#Index(nodes#0, p#9)): DatatypeType } 
                    true
                       ==> 
                      LitInt(0) <= p#9 && p#9 < Seq#Length(Lit(g#0))
                       ==> ($Unbox(Seq#Index(Lit(g#0), p#9)): int >= LitInt(0)
                         <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(Lit(nodes#0), p#9)): DatatypeType))))
                   ==> 
                  (forall p#10: int :: 
                    { $Unbox(Seq#Index(g#0, p#10)): int } 
                    true
                       ==> 
                      LitInt(0) <= p#10
                         && p#10 < Seq#Length(Lit(g#0))
                         && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#10)): int
                       ==> 
                      $Unbox(Seq#Index(Lit(g#0), p#10)): int == _module.__default.sentinel()
                       ==> p#10 == LitInt(0))
                   ==> (forall p#11: int :: 
                      { $Unbox(Seq#Index(g#0, p#11)): int } 
                        { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#11)): int)): int } 
                        { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#11)): int) } 
                      LitInt(0) <= p#11
                         ==> 
                        p#11 < Seq#Length(Lit(g#0))
                         ==> 
                        _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#11)): int
                         ==> 
                        LitInt(0) <= $Unbox(Seq#Index(Lit(g#0), p#11)): int
                         ==> 
                        $Unbox(Seq#Index(Lit(f#0), $Unbox(Seq#Index(Lit(g#0), p#11)): int)): int == p#11
                         ==> $IsA#_module.Option(_module.Node.data($Unbox(Seq#Index(Lit(nodes#0), p#11)): DatatypeType))
                           && _module.Node.Node_q($Unbox(Seq#Index(Lit(nodes#0), p#11)): DatatypeType))
                     && ((forall p#11: int :: 
                        { $Unbox(Seq#Index(g#0, p#11)): int } 
                          { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#11)): int)): int } 
                          { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#11)): int) } 
                        true
                           ==> 
                          LitInt(0) <= p#11
                             && p#11 < Seq#Length(Lit(g#0))
                             && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#11)): int
                           ==> 
                          LitInt(0) <= $Unbox(Seq#Index(Lit(g#0), p#11)): int
                           ==> $Unbox(Seq#Index(Lit(f#0), $Unbox(Seq#Index(Lit(g#0), p#11)): int)): int == p#11
                             && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(Lit(nodes#0), p#11)): DatatypeType), 
                              #_module.Option.Some(Seq#Index(Lit(s#0), $Unbox(Seq#Index(Lit(g#0), p#11)): int))))
                       ==> (forall p#12: int :: 
                          { $Unbox(Seq#Index(g#0, p#12)): int } 
                            { _module.Node.next($Unbox(Seq#Index(nodes#0, p#12)): DatatypeType) } 
                          LitInt(0) <= p#12
                             ==> 
                            p#12 < Seq#Length(Lit(g#0))
                             ==> 
                            _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#12)): int
                             ==> _module.Node.Node_q($Unbox(Seq#Index(Lit(nodes#0), p#12)): DatatypeType)
                               && 
                              _module.__default.Add#canCall($Unbox(Seq#Index(Lit(g#0), p#12)): int, LitInt(1))
                               && (_module.__default.Add($Unbox(Seq#Index(Lit(g#0), p#12)): int, LitInt(1))
                                   < Seq#Length(Lit(f#0))
                                 ==> _module.__default.Add#canCall($Unbox(Seq#Index(Lit(g#0), p#12)): int, LitInt(1))))
                         && ((forall p#12: int :: 
                            { $Unbox(Seq#Index(g#0, p#12)): int } 
                              { _module.Node.next($Unbox(Seq#Index(nodes#0, p#12)): DatatypeType) } 
                            true
                               ==> 
                              LitInt(0) <= p#12
                                 && p#12 < Seq#Length(Lit(g#0))
                                 && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#12)): int
                               ==> _module.Node.next($Unbox(Seq#Index(Lit(nodes#0), p#12)): DatatypeType)
                                 == (if _module.__default.Add($Unbox(Seq#Index(Lit(g#0), p#12)): int, LitInt(1))
                                     < Seq#Length(Lit(f#0))
                                   then $Unbox(Seq#Index(Lit(f#0), 
                                      _module.__default.Add($Unbox(Seq#Index(Lit(g#0), p#12)): int, LitInt(1)))): int
                                   else 0))
                           ==> (forall p#13: int :: 
                            { $Unbox(Seq#Index(g#0, p#13)): int } 
                              { _module.Node.prev($Unbox(Seq#Index(nodes#0, p#13)): DatatypeType) } 
                            (LitInt(0) <= p#13
                                 && p#13 < Seq#Length(Lit(g#0))
                                 && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#13)): int
                               ==> true)
                               ==> 
                              LitInt(0) <= p#13
                               ==> 
                              p#13 < Seq#Length(Lit(g#0))
                               ==> 
                              _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#13)): int
                               ==> _module.Node.Node_q($Unbox(Seq#Index(Lit(nodes#0), p#13)): DatatypeType)
                                 && 
                                ($Unbox(Seq#Index(Lit(g#0), p#13)): int > 0
                                   ==> _module.__default.Sub#canCall($Unbox(Seq#Index(Lit(g#0), p#13)): int, LitInt(1)))
                                 && (0 >= $Unbox(Seq#Index(Lit(g#0), p#13)): int
                                   ==> 
                                  !($Unbox(Seq#Index(Lit(g#0), p#13)): int == LitInt(0)
                                     || Seq#Length(Lit(f#0)) == LitInt(0))
                                   ==> _module.__default.Sub#canCall(Seq#Length(Lit(f#0)), LitInt(1)))))))))
         && _module.__default.Invs(_module._default.Invs$A, 
            Lit(nodes#0), 
            LitInt(freeStack#0), 
            Lit(s#0), 
            Lit(f#0), 
            Lit(g#0))
           == (
            Seq#Length(Lit(f#0)) == Seq#Length(Lit(s#0))
             && Seq#Length(Lit(g#0)) == Seq#Length(Lit(nodes#0))
             && Seq#Length(Lit(nodes#0)) > 0
             && $Unbox(Seq#Index(Lit(g#0), LitInt(0))): int == _module.__default.sentinel()
             && 
            LitInt(0) <= LitInt(freeStack#0)
             && freeStack#0 < Seq#Length(Lit(nodes#0))
             && (forall i#2: int :: 
              { $Unbox(Seq#Index(f#0, i#2)): int } 
              true
                 ==> (LitInt(0) <= i#2 && i#2 < Seq#Length(Lit(f#0))
                     ==> 0 < $Unbox(Seq#Index(Lit(f#0), i#2)): int)
                   && (LitInt(0) <= i#2 && i#2 < Seq#Length(Lit(f#0))
                     ==> $Unbox(Seq#Index(Lit(f#0), i#2)): int < Seq#Length(Lit(nodes#0))))
             && (forall i#3: int :: 
              { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#3)): int)): int } 
              true
                 ==> 
                LitInt(0) <= i#3 && i#3 < Seq#Length(Lit(f#0))
                 ==> $Unbox(Seq#Index(Lit(g#0), $Unbox(Seq#Index(Lit(f#0), i#3)): int)): int == i#3)
             && (forall p#7: int :: 
              { $Unbox(Seq#Index(g#0, p#7)): int } 
              true
                 ==> (LitInt(0) <= p#7 && p#7 < Seq#Length(Lit(g#0))
                     ==> _module.__default.unused() <= $Unbox(Seq#Index(Lit(g#0), p#7)): int)
                   && (LitInt(0) <= p#7 && p#7 < Seq#Length(Lit(g#0))
                     ==> $Unbox(Seq#Index(Lit(g#0), p#7)): int < Seq#Length(Lit(s#0))))
             && (forall p#8: int :: 
              { $Unbox(Seq#Index(nodes#0, p#8)): DatatypeType } 
              true
                 ==> (LitInt(0) <= p#8 && p#8 < Seq#Length(Lit(g#0))
                     ==> LitInt(0)
                       <= _module.Node.next($Unbox(Seq#Index(Lit(nodes#0), p#8)): DatatypeType))
                   && (LitInt(0) <= p#8 && p#8 < Seq#Length(Lit(g#0))
                     ==> _module.Node.next($Unbox(Seq#Index(Lit(nodes#0), p#8)): DatatypeType)
                       < Seq#Length(Lit(g#0))))
             && (forall p#9: int :: 
              { $Unbox(Seq#Index(g#0, p#9)): int } 
                { $Unbox(Seq#Index(nodes#0, p#9)): DatatypeType } 
              true
                 ==> 
                LitInt(0) <= p#9 && p#9 < Seq#Length(Lit(g#0))
                 ==> ($Unbox(Seq#Index(Lit(g#0), p#9)): int >= LitInt(0)
                   <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(Lit(nodes#0), p#9)): DatatypeType))))
             && (forall p#10: int :: 
              { $Unbox(Seq#Index(g#0, p#10)): int } 
              true
                 ==> 
                LitInt(0) <= p#10
                   && p#10 < Seq#Length(Lit(g#0))
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#10)): int
                 ==> 
                $Unbox(Seq#Index(Lit(g#0), p#10)): int == _module.__default.sentinel()
                 ==> p#10 == LitInt(0))
             && (forall p#11: int :: 
              { $Unbox(Seq#Index(g#0, p#11)): int } 
                { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#11)): int)): int } 
                { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#11)): int) } 
              true
                 ==> 
                LitInt(0) <= p#11
                   && p#11 < Seq#Length(Lit(g#0))
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#11)): int
                 ==> 
                LitInt(0) <= $Unbox(Seq#Index(Lit(g#0), p#11)): int
                 ==> $Unbox(Seq#Index(Lit(f#0), $Unbox(Seq#Index(Lit(g#0), p#11)): int)): int == p#11
                   && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(Lit(nodes#0), p#11)): DatatypeType), 
                    #_module.Option.Some(Seq#Index(Lit(s#0), $Unbox(Seq#Index(Lit(g#0), p#11)): int))))
             && (forall p#12: int :: 
              { $Unbox(Seq#Index(g#0, p#12)): int } 
                { _module.Node.next($Unbox(Seq#Index(nodes#0, p#12)): DatatypeType) } 
              true
                 ==> 
                LitInt(0) <= p#12
                   && p#12 < Seq#Length(Lit(g#0))
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#12)): int
                 ==> _module.Node.next($Unbox(Seq#Index(Lit(nodes#0), p#12)): DatatypeType)
                   == (if _module.__default.Add($Unbox(Seq#Index(Lit(g#0), p#12)): int, LitInt(1))
                       < Seq#Length(Lit(f#0))
                     then $Unbox(Seq#Index(Lit(f#0), 
                        _module.__default.Add($Unbox(Seq#Index(Lit(g#0), p#12)): int, LitInt(1)))): int
                     else 0))
             && (forall p#13: int :: 
              { $Unbox(Seq#Index(g#0, p#13)): int } 
                { _module.Node.prev($Unbox(Seq#Index(nodes#0, p#13)): DatatypeType) } 
              true
                 ==> (LitInt(0) <= p#13
                       && p#13 < Seq#Length(Lit(g#0))
                       && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#13)): int
                     ==> true)
                   && (LitInt(0) <= p#13
                       && p#13 < Seq#Length(Lit(g#0))
                       && _module.__default.sentinel() <= $Unbox(Seq#Index(Lit(g#0), p#13)): int
                     ==> _module.Node.prev($Unbox(Seq#Index(Lit(nodes#0), p#13)): DatatypeType)
                       == (if $Unbox(Seq#Index(Lit(g#0), p#13)): int > 0
                         then $Unbox(Seq#Index(Lit(f#0), 
                            _module.__default.Sub($Unbox(Seq#Index(Lit(g#0), p#13)): int, LitInt(1)))): int
                         else (if $Unbox(Seq#Index(Lit(g#0), p#13)): int == LitInt(0)
                             || Seq#Length(Lit(f#0)) == LitInt(0)
                           then 0
                           else $Unbox(Seq#Index(Lit(f#0), _module.__default.Sub(Seq#Length(Lit(f#0)), LitInt(1)))): int))))));

procedure CheckWellformed$$_module.__default.Invs(_module._default.Invs$A: Ty, 
    nodes#0: Seq Box
       where $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Invs$A))), 
    freeStack#0: int, 
    s#0: Seq Box where $Is(s#0, TSeq(_module._default.Invs$A)), 
    f#0: Seq Box where $Is(f#0, TSeq(TInt)), 
    g#0: Seq Box where $Is(g#0, TSeq(TInt)));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Invs(_module._default.Invs$A: Ty, 
    nodes#0: Seq Box, 
    freeStack#0: int, 
    s#0: Seq Box, 
    f#0: Seq Box, 
    g#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#4: int;
  var i#5: int;
  var p#14: int;
  var p#15: int;
  var p#17: int;
  var p#19: int;
  var p#21: int;
  var p#23: int;
  var ##a#0: int;
  var ##b#0: int;
  var ##a#1: int;
  var ##b#1: int;
  var p#25: int;
  var ##a#2: int;
  var ##b#2: int;
  var ##a#3: int;
  var ##b#3: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function Invs
    assume {:captureState "DLL_Dafny.dfy(88,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (Seq#Length(f#0) == Seq#Length(s#0))
        {
        }

        if (Seq#Length(f#0) == Seq#Length(s#0) && Seq#Length(g#0) == Seq#Length(nodes#0))
        {
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0)
        {
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(g#0);
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel())
        {
            if (LitInt(0) <= freeStack#0)
            {
            }
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0))
        {
            havoc i#4;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#4)
            {
            }

            if (LitInt(0) <= i#4 && i#4 < Seq#Length(f#0))
            {
                assert 0 <= i#4 && i#4 < Seq#Length(f#0);
                if (0 < $Unbox(Seq#Index(f#0, i#4)): int)
                {
                    assert 0 <= i#4 && i#4 < Seq#Length(f#0);
                }
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0))))
        {
            havoc i#5;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#5)
            {
            }

            if (LitInt(0) <= i#5 && i#5 < Seq#Length(f#0))
            {
                assert 0 <= i#5 && i#5 < Seq#Length(f#0);
                assert 0 <= $Unbox(Seq#Index(f#0, i#5)): int
                   && $Unbox(Seq#Index(f#0, i#5)): int < Seq#Length(g#0);
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           && (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7))
        {
            havoc p#14;
            // Begin Comprehension WF check
            if (LitInt(0) <= p#14)
            {
            }

            if (LitInt(0) <= p#14 && p#14 < Seq#Length(g#0))
            {
                assert 0 <= p#14 && p#14 < Seq#Length(g#0);
                if (_module.__default.unused() <= $Unbox(Seq#Index(g#0, p#14)): int)
                {
                    assert 0 <= p#14 && p#14 < Seq#Length(g#0);
                }
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           && (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
           && (forall p#16: int :: 
            { $Unbox(Seq#Index(g#0, p#16)): int } 
            true
               ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                 && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0))))
        {
            havoc p#15;
            // Begin Comprehension WF check
            if (LitInt(0) <= p#15)
            {
            }

            if (LitInt(0) <= p#15 && p#15 < Seq#Length(g#0))
            {
                assert 0 <= p#15 && p#15 < Seq#Length(nodes#0);
                assume _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#15)): DatatypeType);
                if (LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#15)): DatatypeType))
                {
                    assert 0 <= p#15 && p#15 < Seq#Length(nodes#0);
                    assume _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#15)): DatatypeType);
                }
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           && (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
           && (forall p#16: int :: 
            { $Unbox(Seq#Index(g#0, p#16)): int } 
            true
               ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                 && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0)))
           && (forall p#18: int :: 
            { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                 && (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)
                     < Seq#Length(g#0))))
        {
            havoc p#17;
            // Begin Comprehension WF check
            if (LitInt(0) <= p#17)
            {
            }

            if (LitInt(0) <= p#17 && p#17 < Seq#Length(g#0))
            {
                assert 0 <= p#17 && p#17 < Seq#Length(g#0);
                assert 0 <= p#17 && p#17 < Seq#Length(nodes#0);
                assume _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#17)): DatatypeType);
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           && (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
           && (forall p#16: int :: 
            { $Unbox(Seq#Index(g#0, p#16)): int } 
            true
               ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                 && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0)))
           && (forall p#18: int :: 
            { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                 && (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)
                     < Seq#Length(g#0)))
           && (forall p#20: int :: 
            { $Unbox(Seq#Index(g#0, p#20)): int } 
              { $Unbox(Seq#Index(nodes#0, p#20)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#20 && p#20 < Seq#Length(g#0)
               ==> ($Unbox(Seq#Index(g#0, p#20)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#20)): DatatypeType)))))
        {
            havoc p#19;
            // Begin Comprehension WF check
            if (LitInt(0) <= p#19)
            {
            }

            if (LitInt(0) <= p#19 && p#19 < Seq#Length(g#0))
            {
                assert 0 <= p#19 && p#19 < Seq#Length(g#0);
            }

            if (LitInt(0) <= p#19
               && p#19 < Seq#Length(g#0)
               && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#19)): int)
            {
                assert 0 <= p#19 && p#19 < Seq#Length(g#0);
                if ($Unbox(Seq#Index(g#0, p#19)): int == _module.__default.sentinel())
                {
                }
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           && (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
           && (forall p#16: int :: 
            { $Unbox(Seq#Index(g#0, p#16)): int } 
            true
               ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                 && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0)))
           && (forall p#18: int :: 
            { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                 && (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)
                     < Seq#Length(g#0)))
           && (forall p#20: int :: 
            { $Unbox(Seq#Index(g#0, p#20)): int } 
              { $Unbox(Seq#Index(nodes#0, p#20)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#20 && p#20 < Seq#Length(g#0)
               ==> ($Unbox(Seq#Index(g#0, p#20)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#20)): DatatypeType))))
           && (forall p#22: int :: 
            { $Unbox(Seq#Index(g#0, p#22)): int } 
            true
               ==> 
              LitInt(0) <= p#22
                 && p#22 < Seq#Length(g#0)
                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#22)): int
               ==> 
              $Unbox(Seq#Index(g#0, p#22)): int == _module.__default.sentinel()
               ==> p#22 == LitInt(0)))
        {
            havoc p#21;
            // Begin Comprehension WF check
            if (LitInt(0) <= p#21)
            {
            }

            if (LitInt(0) <= p#21 && p#21 < Seq#Length(g#0))
            {
                assert 0 <= p#21 && p#21 < Seq#Length(g#0);
            }

            if (LitInt(0) <= p#21
               && p#21 < Seq#Length(g#0)
               && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#21)): int)
            {
                assert 0 <= p#21 && p#21 < Seq#Length(g#0);
                if (LitInt(0) <= $Unbox(Seq#Index(g#0, p#21)): int)
                {
                    assert 0 <= p#21 && p#21 < Seq#Length(g#0);
                    assert 0 <= $Unbox(Seq#Index(g#0, p#21)): int
                       && $Unbox(Seq#Index(g#0, p#21)): int < Seq#Length(f#0);
                    if ($Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#21)): int)): int == p#21)
                    {
                        assert 0 <= p#21 && p#21 < Seq#Length(nodes#0);
                        assume _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#21)): DatatypeType);
                        assert 0 <= p#21 && p#21 < Seq#Length(g#0);
                        assert 0 <= $Unbox(Seq#Index(g#0, p#21)): int
                           && $Unbox(Seq#Index(g#0, p#21)): int < Seq#Length(s#0);
                    }
                }
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           && (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
           && (forall p#16: int :: 
            { $Unbox(Seq#Index(g#0, p#16)): int } 
            true
               ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                 && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0)))
           && (forall p#18: int :: 
            { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                 && (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)
                     < Seq#Length(g#0)))
           && (forall p#20: int :: 
            { $Unbox(Seq#Index(g#0, p#20)): int } 
              { $Unbox(Seq#Index(nodes#0, p#20)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#20 && p#20 < Seq#Length(g#0)
               ==> ($Unbox(Seq#Index(g#0, p#20)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#20)): DatatypeType))))
           && (forall p#22: int :: 
            { $Unbox(Seq#Index(g#0, p#22)): int } 
            true
               ==> 
              LitInt(0) <= p#22
                 && p#22 < Seq#Length(g#0)
                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#22)): int
               ==> 
              $Unbox(Seq#Index(g#0, p#22)): int == _module.__default.sentinel()
               ==> p#22 == LitInt(0))
           && (forall p#24: int :: 
            { $Unbox(Seq#Index(g#0, p#24)): int } 
              { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int } 
              { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int) } 
            true
               ==> 
              LitInt(0) <= p#24
                 && p#24 < Seq#Length(g#0)
                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#24)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(g#0, p#24)): int
               ==> $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int == p#24
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(nodes#0, p#24)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int)))))
        {
            havoc p#23;
            // Begin Comprehension WF check
            if (LitInt(0) <= p#23)
            {
            }

            if (LitInt(0) <= p#23 && p#23 < Seq#Length(g#0))
            {
                assert 0 <= p#23 && p#23 < Seq#Length(g#0);
            }

            if (LitInt(0) <= p#23
               && p#23 < Seq#Length(g#0)
               && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#23)): int)
            {
                assert 0 <= p#23 && p#23 < Seq#Length(nodes#0);
                assume _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#23)): DatatypeType);
                assert 0 <= p#23 && p#23 < Seq#Length(g#0);
                ##a#0 := $Unbox(Seq#Index(g#0, p#23)): int;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, TInt, $Heap);
                ##b#0 := LitInt(1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, TInt, $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, p#23)): int, LitInt(1));
                if (_module.__default.Add($Unbox(Seq#Index(g#0, p#23)): int, LitInt(1))
                   < Seq#Length(f#0))
                {
                    assert 0 <= p#23 && p#23 < Seq#Length(g#0);
                    ##a#1 := $Unbox(Seq#Index(g#0, p#23)): int;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##a#1, TInt, $Heap);
                    ##b#1 := LitInt(1);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##b#1, TInt, $Heap);
                    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, p#23)): int, LitInt(1));
                    assert 0 <= _module.__default.Add($Unbox(Seq#Index(g#0, p#23)): int, LitInt(1))
                       && _module.__default.Add($Unbox(Seq#Index(g#0, p#23)): int, LitInt(1))
                         < Seq#Length(f#0);
                }
                else
                {
                }
            }

            // End Comprehension WF check
        }

        if (Seq#Length(f#0) == Seq#Length(s#0)
           && Seq#Length(g#0) == Seq#Length(nodes#0)
           && Seq#Length(nodes#0) > 0
           && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           && 
          LitInt(0) <= freeStack#0
           && freeStack#0 < Seq#Length(nodes#0)
           && (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           && (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
           && (forall p#16: int :: 
            { $Unbox(Seq#Index(g#0, p#16)): int } 
            true
               ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                 && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0)))
           && (forall p#18: int :: 
            { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                 && (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)
                     < Seq#Length(g#0)))
           && (forall p#20: int :: 
            { $Unbox(Seq#Index(g#0, p#20)): int } 
              { $Unbox(Seq#Index(nodes#0, p#20)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#20 && p#20 < Seq#Length(g#0)
               ==> ($Unbox(Seq#Index(g#0, p#20)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#20)): DatatypeType))))
           && (forall p#22: int :: 
            { $Unbox(Seq#Index(g#0, p#22)): int } 
            true
               ==> 
              LitInt(0) <= p#22
                 && p#22 < Seq#Length(g#0)
                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#22)): int
               ==> 
              $Unbox(Seq#Index(g#0, p#22)): int == _module.__default.sentinel()
               ==> p#22 == LitInt(0))
           && (forall p#24: int :: 
            { $Unbox(Seq#Index(g#0, p#24)): int } 
              { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int } 
              { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int) } 
            true
               ==> 
              LitInt(0) <= p#24
                 && p#24 < Seq#Length(g#0)
                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#24)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(g#0, p#24)): int
               ==> $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int == p#24
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(nodes#0, p#24)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int))))
           && (forall p#26: int :: 
            { $Unbox(Seq#Index(g#0, p#26)): int } 
              { _module.Node.next($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#26
                 && p#26 < Seq#Length(g#0)
                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#26)): int
               ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1))
                     < Seq#Length(f#0)
                   then $Unbox(Seq#Index(f#0, _module.__default.Add($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1)))): int
                   else 0)))
        {
            havoc p#25;
            // Begin Comprehension WF check
            if (LitInt(0) <= p#25)
            {
            }

            if (LitInt(0) <= p#25 && p#25 < Seq#Length(g#0))
            {
                assert 0 <= p#25 && p#25 < Seq#Length(g#0);
            }

            if (LitInt(0) <= p#25
               && p#25 < Seq#Length(g#0)
               && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#25)): int)
            {
                if (Lit(true))
                {
                    assert 0 <= p#25 && p#25 < Seq#Length(nodes#0);
                    assume _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#25)): DatatypeType);
                    assert 0 <= p#25 && p#25 < Seq#Length(g#0);
                    if ($Unbox(Seq#Index(g#0, p#25)): int > 0)
                    {
                        assert 0 <= p#25 && p#25 < Seq#Length(g#0);
                        ##a#2 := $Unbox(Seq#Index(g#0, p#25)): int;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##a#2, TInt, $Heap);
                        ##b#2 := LitInt(1);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##b#2, TInt, $Heap);
                        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assume _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, p#25)): int, LitInt(1));
                        assert 0 <= _module.__default.Sub($Unbox(Seq#Index(g#0, p#25)): int, LitInt(1))
                           && _module.__default.Sub($Unbox(Seq#Index(g#0, p#25)): int, LitInt(1))
                             < Seq#Length(f#0);
                    }
                    else
                    {
                        assert 0 <= p#25 && p#25 < Seq#Length(g#0);
                        if ($Unbox(Seq#Index(g#0, p#25)): int != LitInt(0))
                        {
                        }

                        if ($Unbox(Seq#Index(g#0, p#25)): int == LitInt(0) || Seq#Length(f#0) == LitInt(0))
                        {
                        }
                        else
                        {
                            ##a#3 := Seq#Length(f#0);
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##a#3, TInt, $Heap);
                            ##b#3 := LitInt(1);
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##b#3, TInt, $Heap);
                            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                            assume _module.__default.Sub#canCall(Seq#Length(f#0), LitInt(1));
                            assert 0 <= _module.__default.Sub(Seq#Length(f#0), LitInt(1))
                               && _module.__default.Sub(Seq#Length(f#0), LitInt(1)) < Seq#Length(f#0);
                        }
                    }
                }
            }

            // End Comprehension WF check
        }

        assume _module.__default.Invs(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0)
           == (
            Seq#Length(f#0) == Seq#Length(s#0)
             && Seq#Length(g#0) == Seq#Length(nodes#0)
             && Seq#Length(nodes#0) > 0
             && $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
             && 
            LitInt(0) <= freeStack#0
             && freeStack#0 < Seq#Length(nodes#0)
             && (forall i#6: int :: 
              { $Unbox(Seq#Index(f#0, i#6)): int } 
              true
                 ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                     ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                   && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                     ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
             && (forall i#7: int :: 
              { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
              true
                 ==> 
                LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
                 ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
             && (forall p#16: int :: 
              { $Unbox(Seq#Index(g#0, p#16)): int } 
              true
                 ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                     ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                   && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                     ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0)))
             && (forall p#18: int :: 
              { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
              true
                 ==> (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                     ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                   && (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                     ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)
                       < Seq#Length(g#0)))
             && (forall p#20: int :: 
              { $Unbox(Seq#Index(g#0, p#20)): int } 
                { $Unbox(Seq#Index(nodes#0, p#20)): DatatypeType } 
              true
                 ==> 
                LitInt(0) <= p#20 && p#20 < Seq#Length(g#0)
                 ==> ($Unbox(Seq#Index(g#0, p#20)): int >= LitInt(0)
                   <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#20)): DatatypeType))))
             && (forall p#22: int :: 
              { $Unbox(Seq#Index(g#0, p#22)): int } 
              true
                 ==> 
                LitInt(0) <= p#22
                   && p#22 < Seq#Length(g#0)
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#22)): int
                 ==> 
                $Unbox(Seq#Index(g#0, p#22)): int == _module.__default.sentinel()
                 ==> p#22 == LitInt(0))
             && (forall p#24: int :: 
              { $Unbox(Seq#Index(g#0, p#24)): int } 
                { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int } 
                { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int) } 
              true
                 ==> 
                LitInt(0) <= p#24
                   && p#24 < Seq#Length(g#0)
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#24)): int
                 ==> 
                LitInt(0) <= $Unbox(Seq#Index(g#0, p#24)): int
                 ==> $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int == p#24
                   && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(nodes#0, p#24)): DatatypeType), 
                    #_module.Option.Some(Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int))))
             && (forall p#26: int :: 
              { $Unbox(Seq#Index(g#0, p#26)): int } 
                { _module.Node.next($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType) } 
              true
                 ==> 
                LitInt(0) <= p#26
                   && p#26 < Seq#Length(g#0)
                   && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#26)): int
                 ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType)
                   == (if _module.__default.Add($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1))
                       < Seq#Length(f#0)
                     then $Unbox(Seq#Index(f#0, _module.__default.Add($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1)))): int
                     else 0))
             && (forall p#27: int :: 
              { $Unbox(Seq#Index(g#0, p#27)): int } 
                { _module.Node.prev($Unbox(Seq#Index(nodes#0, p#27)): DatatypeType) } 
              true
                 ==> (LitInt(0) <= p#27
                       && p#27 < Seq#Length(g#0)
                       && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#27)): int
                     ==> true)
                   && (LitInt(0) <= p#27
                       && p#27 < Seq#Length(g#0)
                       && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#27)): int
                     ==> _module.Node.prev($Unbox(Seq#Index(nodes#0, p#27)): DatatypeType)
                       == (if $Unbox(Seq#Index(g#0, p#27)): int > 0
                         then $Unbox(Seq#Index(f#0, _module.__default.Sub($Unbox(Seq#Index(g#0, p#27)): int, LitInt(1)))): int
                         else (if $Unbox(Seq#Index(g#0, p#27)): int == LitInt(0) || Seq#Length(f#0) == LitInt(0)
                           then 0
                           else $Unbox(Seq#Index(f#0, _module.__default.Sub(Seq#Length(f#0), LitInt(1)))): int)))));
        assume Seq#Length(f#0) == Seq#Length(s#0)
           ==> 
          Seq#Length(g#0) == Seq#Length(nodes#0)
           ==> 
          Seq#Length(nodes#0) > 0
           ==> 
          $Unbox(Seq#Index(g#0, LitInt(0))): int == _module.__default.sentinel()
           ==> 
          LitInt(0) <= freeStack#0 && freeStack#0 < Seq#Length(nodes#0)
           ==> 
          (forall i#6: int :: 
            { $Unbox(Seq#Index(f#0, i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> 0 < $Unbox(Seq#Index(f#0, i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(f#0)
                   ==> $Unbox(Seq#Index(f#0, i#6)): int < Seq#Length(nodes#0)))
           ==> 
          (forall i#7: int :: 
            { $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(f#0)
               ==> $Unbox(Seq#Index(g#0, $Unbox(Seq#Index(f#0, i#7)): int)): int == i#7)
           ==> 
          (forall p#16: int :: 
            { $Unbox(Seq#Index(g#0, p#16)): int } 
            true
               ==> (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(g#0, p#16)): int)
                 && (LitInt(0) <= p#16 && p#16 < Seq#Length(g#0)
                   ==> $Unbox(Seq#Index(g#0, p#16)): int < Seq#Length(s#0)))
           ==> (forall p#18: int :: 
              { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
              (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                 && (
                  (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                   ==> 
                  LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                   ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)))
             && ((forall p#18: int :: 
                { $Unbox(Seq#Index(nodes#0, p#18)): DatatypeType } 
                true
                   ==> (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                       ==> LitInt(0) <= _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType))
                     && (LitInt(0) <= p#18 && p#18 < Seq#Length(g#0)
                       ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#18)): DatatypeType)
                         < Seq#Length(g#0)))
               ==> (forall p#20: int :: 
                  { $Unbox(Seq#Index(g#0, p#20)): int } 
                    { $Unbox(Seq#Index(nodes#0, p#20)): DatatypeType } 
                  LitInt(0) <= p#20 && p#20 < Seq#Length(g#0)
                     ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#20)): DatatypeType))
                 && ((forall p#20: int :: 
                    { $Unbox(Seq#Index(g#0, p#20)): int } 
                      { $Unbox(Seq#Index(nodes#0, p#20)): DatatypeType } 
                    true
                       ==> 
                      LitInt(0) <= p#20 && p#20 < Seq#Length(g#0)
                       ==> ($Unbox(Seq#Index(g#0, p#20)): int >= LitInt(0)
                         <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(nodes#0, p#20)): DatatypeType))))
                   ==> 
                  (forall p#22: int :: 
                    { $Unbox(Seq#Index(g#0, p#22)): int } 
                    true
                       ==> 
                      LitInt(0) <= p#22
                         && p#22 < Seq#Length(g#0)
                         && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#22)): int
                       ==> 
                      $Unbox(Seq#Index(g#0, p#22)): int == _module.__default.sentinel()
                       ==> p#22 == LitInt(0))
                   ==> (forall p#24: int :: 
                      { $Unbox(Seq#Index(g#0, p#24)): int } 
                        { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int } 
                        { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int) } 
                      LitInt(0) <= p#24 && p#24 < Seq#Length(g#0)
                         ==> 
                        _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#24)): int
                         ==> 
                        LitInt(0) <= $Unbox(Seq#Index(g#0, p#24)): int
                         ==> 
                        $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int == p#24
                         ==> $IsA#_module.Option(_module.Node.data($Unbox(Seq#Index(nodes#0, p#24)): DatatypeType))
                           && _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#24)): DatatypeType))
                     && ((forall p#24: int :: 
                        { $Unbox(Seq#Index(g#0, p#24)): int } 
                          { $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int } 
                          { Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int) } 
                        true
                           ==> 
                          LitInt(0) <= p#24
                             && p#24 < Seq#Length(g#0)
                             && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#24)): int
                           ==> 
                          LitInt(0) <= $Unbox(Seq#Index(g#0, p#24)): int
                           ==> $Unbox(Seq#Index(f#0, $Unbox(Seq#Index(g#0, p#24)): int)): int == p#24
                             && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(nodes#0, p#24)): DatatypeType), 
                              #_module.Option.Some(Seq#Index(s#0, $Unbox(Seq#Index(g#0, p#24)): int))))
                       ==> (forall p#26: int :: 
                          { $Unbox(Seq#Index(g#0, p#26)): int } 
                            { _module.Node.next($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType) } 
                          LitInt(0) <= p#26 && p#26 < Seq#Length(g#0)
                             ==> 
                            _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#26)): int
                             ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType)
                               && 
                              _module.__default.Add#canCall($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1))
                               && (_module.__default.Add($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1))
                                   < Seq#Length(f#0)
                                 ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1))))
                         && ((forall p#26: int :: 
                            { $Unbox(Seq#Index(g#0, p#26)): int } 
                              { _module.Node.next($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType) } 
                            true
                               ==> 
                              LitInt(0) <= p#26
                                 && p#26 < Seq#Length(g#0)
                                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#26)): int
                               ==> _module.Node.next($Unbox(Seq#Index(nodes#0, p#26)): DatatypeType)
                                 == (if _module.__default.Add($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1))
                                     < Seq#Length(f#0)
                                   then $Unbox(Seq#Index(f#0, _module.__default.Add($Unbox(Seq#Index(g#0, p#26)): int, LitInt(1)))): int
                                   else 0))
                           ==> (forall p#27: int :: 
                            { $Unbox(Seq#Index(g#0, p#27)): int } 
                              { _module.Node.prev($Unbox(Seq#Index(nodes#0, p#27)): DatatypeType) } 
                            (LitInt(0) <= p#27
                                 && p#27 < Seq#Length(g#0)
                                 && _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#27)): int
                               ==> true)
                               ==> 
                              LitInt(0) <= p#27 && p#27 < Seq#Length(g#0)
                               ==> 
                              _module.__default.sentinel() <= $Unbox(Seq#Index(g#0, p#27)): int
                               ==> _module.Node.Node_q($Unbox(Seq#Index(nodes#0, p#27)): DatatypeType)
                                 && 
                                ($Unbox(Seq#Index(g#0, p#27)): int > 0
                                   ==> _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, p#27)): int, LitInt(1)))
                                 && (0 >= $Unbox(Seq#Index(g#0, p#27)): int
                                   ==> 
                                  !($Unbox(Seq#Index(g#0, p#27)): int == LitInt(0) || Seq#Length(f#0) == LitInt(0))
                                   ==> _module.__default.Sub#canCall(Seq#Length(f#0), LitInt(1))))))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Invs(_module._default.Invs$A, nodes#0, freeStack#0, s#0, f#0, g#0), 
          TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module._default.Inv
function _module.__default.Inv(_module._default.Inv$A: Ty, l#0: DatatypeType) : bool;

function _module.__default.Inv#canCall(_module._default.Inv$A: Ty, l#0: DatatypeType) : bool;

// consequence axiom for _module.__default.Inv
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Inv$A: Ty, l#0: DatatypeType :: 
    { _module.__default.Inv(_module._default.Inv$A, l#0) } 
    _module.__default.Inv#canCall(_module._default.Inv$A, l#0)
         || (12 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Inv$A)))
       ==> true);

function _module.__default.Inv#requires(Ty, DatatypeType) : bool;

// #requires axiom for _module.__default.Inv
axiom (forall _module._default.Inv$A: Ty, l#0: DatatypeType :: 
  { _module.__default.Inv#requires(_module._default.Inv$A, l#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.Inv$A))
     ==> _module.__default.Inv#requires(_module._default.Inv$A, l#0) == true);

// definition axiom for _module.__default.Inv (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Inv$A: Ty, l#0: DatatypeType :: 
    { _module.__default.Inv(_module._default.Inv$A, l#0) } 
    _module.__default.Inv#canCall(_module._default.Inv$A, l#0)
         || (12 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Inv$A)))
       ==> _module.DList.DList_q(l#0)
         && _module.DList.DList_q(l#0)
         && _module.DList.DList_q(l#0)
         && _module.DList.DList_q(l#0)
         && _module.DList.DList_q(l#0)
         && _module.__default.Invs#canCall(_module._default.Inv$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         && _module.__default.Inv(_module._default.Inv$A, l#0)
           == _module.__default.Invs(_module._default.Inv$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0)));

// definition axiom for _module.__default.Inv for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Inv$A: Ty, l#0: DatatypeType :: 
    {:weight 3} { _module.__default.Inv(_module._default.Inv$A, Lit(l#0)) } 
    _module.__default.Inv#canCall(_module._default.Inv$A, Lit(l#0))
         || (12 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Inv$A)))
       ==> _module.DList.DList_q(Lit(l#0))
         && _module.DList.DList_q(Lit(l#0))
         && _module.DList.DList_q(Lit(l#0))
         && _module.DList.DList_q(Lit(l#0))
         && _module.DList.DList_q(Lit(l#0))
         && _module.__default.Invs#canCall(_module._default.Inv$A, 
          Lit(_module.DList.nodes(Lit(l#0))), 
          LitInt(_module.DList.freeStack(Lit(l#0))), 
          Lit(_module.DList.s(Lit(l#0))), 
          Lit(_module.DList.f(Lit(l#0))), 
          Lit(_module.DList.g(Lit(l#0))))
         && _module.__default.Inv(_module._default.Inv$A, Lit(l#0))
           == Lit(_module.__default.Invs(_module._default.Inv$A, 
              Lit(_module.DList.nodes(Lit(l#0))), 
              LitInt(_module.DList.freeStack(Lit(l#0))), 
              Lit(_module.DList.s(Lit(l#0))), 
              Lit(_module.DList.f(Lit(l#0))), 
              Lit(_module.DList.g(Lit(l#0))))));

procedure CheckWellformed$$_module.__default.Inv(_module._default.Inv$A: Ty, 
    l#0: DatatypeType where $Is(l#0, Tclass._module.DList(_module._default.Inv$A)));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Inv(_module._default.Inv$A: Ty, l#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##nodes#0: Seq Box;
  var ##freeStack#0: int;
  var ##s#0: Seq Box;
  var ##f#0: Seq Box;
  var ##g#0: Seq Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Inv
    assume {:captureState "DLL_Dafny.dfy(121,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.DList.DList_q(l#0);
        assume _module.DList.DList_q(l#0);
        assume _module.DList.DList_q(l#0);
        assume _module.DList.DList_q(l#0);
        assume _module.DList.DList_q(l#0);
        ##nodes#0 := _module.DList.nodes(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##nodes#0, TSeq(Tclass._module.Node(_module._default.Inv$A)), $Heap);
        ##freeStack#0 := _module.DList.freeStack(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##freeStack#0, TInt, $Heap);
        ##s#0 := _module.DList.s(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, TSeq(_module._default.Inv$A), $Heap);
        ##f#0 := _module.DList.f(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#0, TSeq(TInt), $Heap);
        ##g#0 := _module.DList.g(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##g#0, TSeq(TInt), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Invs#canCall(_module._default.Inv$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0));
        assume _module.__default.Inv(_module._default.Inv$A, l#0)
           == _module.__default.Invs(_module._default.Inv$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0));
        assume _module.DList.DList_q(l#0)
           && _module.DList.DList_q(l#0)
           && _module.DList.DList_q(l#0)
           && _module.DList.DList_q(l#0)
           && _module.DList.DList_q(l#0)
           && _module.__default.Invs#canCall(_module._default.Inv$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Inv(_module._default.Inv$A, l#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Seq
function _module.__default.Seq(_module._default.Seq$A: Ty, l#0: DatatypeType) : Seq Box;

function _module.__default.Seq#canCall(_module._default.Seq$A: Ty, l#0: DatatypeType) : bool;

// consequence axiom for _module.__default.Seq
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.Seq$A: Ty, l#0: DatatypeType :: 
    { _module.__default.Seq(_module._default.Seq$A, l#0) } 
    _module.__default.Seq#canCall(_module._default.Seq$A, l#0)
         || (13 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Seq$A)))
       ==> $Is(_module.__default.Seq(_module._default.Seq$A, l#0), TSeq(_module._default.Seq$A)));

function _module.__default.Seq#requires(Ty, DatatypeType) : bool;

// #requires axiom for _module.__default.Seq
axiom (forall _module._default.Seq$A: Ty, l#0: DatatypeType :: 
  { _module.__default.Seq#requires(_module._default.Seq$A, l#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.Seq$A))
     ==> _module.__default.Seq#requires(_module._default.Seq$A, l#0) == true);

// definition axiom for _module.__default.Seq (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.Seq$A: Ty, l#0: DatatypeType :: 
    { _module.__default.Seq(_module._default.Seq$A, l#0) } 
    _module.__default.Seq#canCall(_module._default.Seq$A, l#0)
         || (13 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Seq$A)))
       ==> _module.DList.DList_q(l#0)
         && _module.__default.Seq(_module._default.Seq$A, l#0) == _module.DList.s(l#0));

// definition axiom for _module.__default.Seq for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.Seq$A: Ty, l#0: DatatypeType :: 
    {:weight 3} { _module.__default.Seq(_module._default.Seq$A, Lit(l#0)) } 
    _module.__default.Seq#canCall(_module._default.Seq$A, Lit(l#0))
         || (13 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Seq$A)))
       ==> _module.DList.DList_q(Lit(l#0))
         && _module.__default.Seq(_module._default.Seq$A, Lit(l#0))
           == Lit(_module.DList.s(Lit(l#0))));

procedure CheckWellformed$$_module.__default.Seq(_module._default.Seq$A: Ty, 
    l#0: DatatypeType where $Is(l#0, Tclass._module.DList(_module._default.Seq$A)));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.ValidPtr
function _module.__default.ValidPtr(_module._default.ValidPtr$A: Ty, l#0: DatatypeType, p#0: int) : bool;

function _module.__default.ValidPtr#canCall(_module._default.ValidPtr$A: Ty, l#0: DatatypeType, p#0: int) : bool;

// consequence axiom for _module.__default.ValidPtr
axiom 14 <= $FunctionContextHeight
   ==> (forall _module._default.ValidPtr$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.ValidPtr(_module._default.ValidPtr$A, l#0, p#0) } 
    _module.__default.ValidPtr#canCall(_module._default.ValidPtr$A, l#0, p#0)
         || (14 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.ValidPtr$A)))
       ==> 
      _module.__default.ValidPtr(_module._default.ValidPtr$A, l#0, p#0)
       ==> p#0 != 0);

function _module.__default.ValidPtr#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.__default.ValidPtr
axiom (forall _module._default.ValidPtr$A: Ty, l#0: DatatypeType, p#0: int :: 
  { _module.__default.ValidPtr#requires(_module._default.ValidPtr$A, l#0, p#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.ValidPtr$A))
     ==> _module.__default.ValidPtr#requires(_module._default.ValidPtr$A, l#0, p#0)
       == true);

// definition axiom for _module.__default.ValidPtr (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall _module._default.ValidPtr$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.ValidPtr(_module._default.ValidPtr$A, l#0, p#0) } 
    _module.__default.ValidPtr#canCall(_module._default.ValidPtr$A, l#0, p#0)
         || (14 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.ValidPtr$A)))
       ==> (0 < p#0
           ==> _module.DList.DList_q(l#0)
             && (p#0 < Seq#Length(_module.DList.g(l#0)) ==> _module.DList.DList_q(l#0)))
         && _module.__default.ValidPtr(_module._default.ValidPtr$A, l#0, p#0)
           == (
            0 < p#0
             && p#0 < Seq#Length(_module.DList.g(l#0))
             && $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int >= LitInt(0)));

// definition axiom for _module.__default.ValidPtr for all literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall _module._default.ValidPtr$A: Ty, l#0: DatatypeType, p#0: int :: 
    {:weight 3} { _module.__default.ValidPtr(_module._default.ValidPtr$A, Lit(l#0), LitInt(p#0)) } 
    _module.__default.ValidPtr#canCall(_module._default.ValidPtr$A, Lit(l#0), LitInt(p#0))
         || (14 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.ValidPtr$A)))
       ==> (Lit(0 < p#0)
           ==> _module.DList.DList_q(Lit(l#0))
             && (p#0 < Seq#Length(Lit(_module.DList.g(Lit(l#0))))
               ==> _module.DList.DList_q(Lit(l#0))))
         && _module.__default.ValidPtr(_module._default.ValidPtr$A, Lit(l#0), LitInt(p#0))
           == (
            0 < p#0
             && p#0 < Seq#Length(Lit(_module.DList.g(Lit(l#0))))
             && $Unbox(Seq#Index(Lit(_module.DList.g(Lit(l#0))), LitInt(p#0))): int >= LitInt(0)));

procedure CheckWellformed$$_module.__default.ValidPtr(_module._default.ValidPtr$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.ValidPtr$A)), 
    p#0: int)
   returns (b#0: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures b#0 ==> p#0 != 0;



implementation CheckWellformed$$_module.__default.ValidPtr(_module._default.ValidPtr$A: Ty, l#0: DatatypeType, p#0: int)
   returns (b#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function ValidPtr
    assume {:captureState "DLL_Dafny.dfy(131,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (*)
        {
            assume b#0;
            assume p#0 != 0;
        }
        else
        {
            assume b#0 ==> p#0 != 0;
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (0 < p#0)
        {
            assume _module.DList.DList_q(l#0);
        }

        if (0 < p#0 && p#0 < Seq#Length(_module.DList.g(l#0)))
        {
            assume _module.DList.DList_q(l#0);
            assert 0 <= p#0 && p#0 < Seq#Length(_module.DList.g(l#0));
        }

        assume _module.__default.ValidPtr(_module._default.ValidPtr$A, l#0, p#0)
           == (
            0 < p#0
             && p#0 < Seq#Length(_module.DList.g(l#0))
             && $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int >= LitInt(0));
        assume (0 < p#0 ==> _module.DList.DList_q(l#0))
           && (0 < p#0 && p#0 < Seq#Length(_module.DList.g(l#0))
             ==> _module.DList.DList_q(l#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ValidPtr(_module._default.ValidPtr$A, l#0, p#0), TBool);
        assume _module.__default.ValidPtr(_module._default.ValidPtr$A, l#0, p#0) == b#0;
    }
}



// function declaration for _module._default.MaybePtr
function _module.__default.MaybePtr(_module._default.MaybePtr$A: Ty, l#0: DatatypeType, p#0: int) : bool;

function _module.__default.MaybePtr#canCall(_module._default.MaybePtr$A: Ty, l#0: DatatypeType, p#0: int) : bool;

// consequence axiom for _module.__default.MaybePtr
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.MaybePtr$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.MaybePtr(_module._default.MaybePtr$A, l#0, p#0) } 
    _module.__default.MaybePtr#canCall(_module._default.MaybePtr$A, l#0, p#0)
         || (15 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.MaybePtr$A)))
       ==> true);

function _module.__default.MaybePtr#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.__default.MaybePtr
axiom (forall _module._default.MaybePtr$A: Ty, l#0: DatatypeType, p#0: int :: 
  { _module.__default.MaybePtr#requires(_module._default.MaybePtr$A, l#0, p#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.MaybePtr$A))
     ==> _module.__default.MaybePtr#requires(_module._default.MaybePtr$A, l#0, p#0)
       == true);

// definition axiom for _module.__default.MaybePtr (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.MaybePtr$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.MaybePtr(_module._default.MaybePtr$A, l#0, p#0) } 
    _module.__default.MaybePtr#canCall(_module._default.MaybePtr$A, l#0, p#0)
         || (15 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.MaybePtr$A)))
       ==> (p#0 != LitInt(0)
           ==> _module.__default.ValidPtr#canCall(_module._default.MaybePtr$A, l#0, p#0))
         && _module.__default.MaybePtr(_module._default.MaybePtr$A, l#0, p#0)
           == (p#0 == LitInt(0)
             || _module.__default.ValidPtr(_module._default.MaybePtr$A, l#0, p#0)));

// definition axiom for _module.__default.MaybePtr for all literals (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.MaybePtr$A: Ty, l#0: DatatypeType, p#0: int :: 
    {:weight 3} { _module.__default.MaybePtr(_module._default.MaybePtr$A, Lit(l#0), LitInt(p#0)) } 
    _module.__default.MaybePtr#canCall(_module._default.MaybePtr$A, Lit(l#0), LitInt(p#0))
         || (15 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.MaybePtr$A)))
       ==> (LitInt(p#0) != LitInt(0)
           ==> _module.__default.ValidPtr#canCall(_module._default.MaybePtr$A, Lit(l#0), LitInt(p#0)))
         && _module.__default.MaybePtr(_module._default.MaybePtr$A, Lit(l#0), LitInt(p#0))
           == (LitInt(p#0) == LitInt(0)
             || _module.__default.ValidPtr(_module._default.MaybePtr$A, Lit(l#0), LitInt(p#0))));

procedure CheckWellformed$$_module.__default.MaybePtr(_module._default.MaybePtr$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.MaybePtr$A)), 
    p#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.MaybePtr(_module._default.MaybePtr$A: Ty, l#0: DatatypeType, p#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##p#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function MaybePtr
    assume {:captureState "DLL_Dafny.dfy(137,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (p#0 != LitInt(0))
        {
            ##l#0 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.MaybePtr$A), $Heap);
            ##p#0 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#0, TInt, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.ValidPtr#canCall(_module._default.MaybePtr$A, l#0, p#0);
        }

        assume _module.__default.MaybePtr(_module._default.MaybePtr$A, l#0, p#0)
           == (p#0 == LitInt(0)
             || _module.__default.ValidPtr(_module._default.MaybePtr$A, l#0, p#0));
        assume p#0 != LitInt(0)
           ==> _module.__default.ValidPtr#canCall(_module._default.MaybePtr$A, l#0, p#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.MaybePtr(_module._default.MaybePtr$A, l#0, p#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Index
function _module.__default.Index(_module._default.Index$A: Ty, l#0: DatatypeType, p#0: int) : int;

function _module.__default.Index#canCall(_module._default.Index$A: Ty, l#0: DatatypeType, p#0: int) : bool;

// consequence axiom for _module.__default.Index
axiom 16 <= $FunctionContextHeight
   ==> (forall _module._default.Index$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Index(_module._default.Index$A, l#0, p#0) } 
    _module.__default.Index#canCall(_module._default.Index$A, l#0, p#0)
         || (16 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Index$A)))
       ==> (_module.__default.Inv(_module._default.Index$A, l#0)
             && _module.__default.ValidPtr(_module._default.Index$A, l#0, p#0)
           ==> LitInt(0) <= _module.__default.Index(_module._default.Index$A, l#0, p#0)
             && _module.__default.Index(_module._default.Index$A, l#0, p#0)
               < Seq#Length(_module.__default.Seq(_module._default.Index$A, l#0)))
         && (_module.__default.Inv(_module._default.Index$A, l#0) && p#0 == LitInt(0)
           ==> _module.__default.Index(_module._default.Index$A, l#0, p#0) == LitInt(0 - 1)));

function _module.__default.Index#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.__default.Index
axiom (forall _module._default.Index$A: Ty, l#0: DatatypeType, p#0: int :: 
  { _module.__default.Index#requires(_module._default.Index$A, l#0, p#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.Index$A))
     ==> _module.__default.Index#requires(_module._default.Index$A, l#0, p#0) == true);

// definition axiom for _module.__default.Index (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall _module._default.Index$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Index(_module._default.Index$A, l#0, p#0) } 
    _module.__default.Index#canCall(_module._default.Index$A, l#0, p#0)
         || (16 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Index$A)))
       ==> _module.__default.Inv#canCall(_module._default.Index$A, l#0)
         && (_module.__default.Inv(_module._default.Index$A, l#0)
           ==> _module.__default.MaybePtr#canCall(_module._default.Index$A, l#0, p#0))
         && (_module.__default.Inv(_module._default.Index$A, l#0)
             && _module.__default.MaybePtr(_module._default.Index$A, l#0, p#0)
           ==> _module.DList.DList_q(l#0))
         && _module.__default.Index(_module._default.Index$A, l#0, p#0)
           == (if _module.__default.Inv(_module._default.Index$A, l#0)
               && _module.__default.MaybePtr(_module._default.Index$A, l#0, p#0)
             then $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int
             else 0));

// definition axiom for _module.__default.Index for all literals (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall _module._default.Index$A: Ty, l#0: DatatypeType, p#0: int :: 
    {:weight 3} { _module.__default.Index(_module._default.Index$A, Lit(l#0), LitInt(p#0)) } 
    _module.__default.Index#canCall(_module._default.Index$A, Lit(l#0), LitInt(p#0))
         || (16 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.Index$A)))
       ==> _module.__default.Inv#canCall(_module._default.Index$A, Lit(l#0))
         && (Lit(_module.__default.Inv(_module._default.Index$A, Lit(l#0)))
           ==> _module.__default.MaybePtr#canCall(_module._default.Index$A, Lit(l#0), LitInt(p#0)))
         && (Lit(_module.__default.Inv(_module._default.Index$A, Lit(l#0))
               && _module.__default.MaybePtr(_module._default.Index$A, Lit(l#0), LitInt(p#0)))
           ==> _module.DList.DList_q(Lit(l#0)))
         && _module.__default.Index(_module._default.Index$A, Lit(l#0), LitInt(p#0))
           == (if _module.__default.Inv(_module._default.Index$A, Lit(l#0))
               && _module.__default.MaybePtr(_module._default.Index$A, Lit(l#0), LitInt(p#0))
             then $Unbox(Seq#Index(Lit(_module.DList.g(Lit(l#0))), LitInt(p#0))): int
             else 0));

procedure CheckWellformed$$_module.__default.Index(_module._default.Index$A: Ty, 
    l#0: DatatypeType where $Is(l#0, Tclass._module.DList(_module._default.Index$A)), 
    p#0: int)
   returns (i#0: int);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.Inv(_module._default.Index$A, l#0)
       && _module.__default.ValidPtr(_module._default.Index$A, l#0, p#0)
     ==> LitInt(0) <= i#0;
  ensures _module.__default.Inv(_module._default.Index$A, l#0)
       && _module.__default.ValidPtr(_module._default.Index$A, l#0, p#0)
     ==> i#0 < Seq#Length(_module.__default.Seq(_module._default.Index$A, l#0));
  ensures _module.__default.Inv(_module._default.Index$A, l#0) && p#0 == LitInt(0)
     ==> i#0 == LitInt(0 - 1);



implementation CheckWellformed$$_module.__default.Index(_module._default.Index$A: Ty, l#0: DatatypeType, p#0: int) returns (i#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var ##l#2: DatatypeType;
  var ##l#3: DatatypeType;
  var ##l#4: DatatypeType;
  var ##l#5: DatatypeType;
  var ##p#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Index
    assume {:captureState "DLL_Dafny.dfy(142,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (*)
        {
            ##l#0 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.Index$A), $Heap);
            assume _module.__default.Inv#canCall(_module._default.Index$A, l#0);
            assume _module.__default.Inv(_module._default.Index$A, l#0);
            ##l#1 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.Index$A), $Heap);
            ##p#0 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#0, TInt, $Heap);
            assume _module.__default.ValidPtr#canCall(_module._default.Index$A, l#0, p#0);
            assume _module.__default.ValidPtr(_module._default.Index$A, l#0, p#0);
            if (LitInt(0) <= i#0)
            {
                ##l#2 := l#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.Index$A), $Heap);
                assume _module.__default.Seq#canCall(_module._default.Index$A, l#0);
            }

            assume LitInt(0) <= i#0
               && i#0 < Seq#Length(_module.__default.Seq(_module._default.Index$A, l#0));
        }
        else
        {
            assume _module.__default.Inv(_module._default.Index$A, l#0)
                 && _module.__default.ValidPtr(_module._default.Index$A, l#0, p#0)
               ==> LitInt(0) <= i#0
                 && i#0 < Seq#Length(_module.__default.Seq(_module._default.Index$A, l#0));
        }

        if (*)
        {
            ##l#3 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.Index$A), $Heap);
            assume _module.__default.Inv#canCall(_module._default.Index$A, l#0);
            assume _module.__default.Inv(_module._default.Index$A, l#0);
            assume p#0 == LitInt(0);
            assume i#0 == LitInt(0 - 1);
        }
        else
        {
            assume _module.__default.Inv(_module._default.Index$A, l#0) && p#0 == LitInt(0)
               ==> i#0 == LitInt(0 - 1);
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##l#4 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#4, Tclass._module.DList(_module._default.Index$A), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Inv#canCall(_module._default.Index$A, l#0);
        if (_module.__default.Inv(_module._default.Index$A, l#0))
        {
            ##l#5 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#5, Tclass._module.DList(_module._default.Index$A), $Heap);
            ##p#1 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#1, TInt, $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.MaybePtr#canCall(_module._default.Index$A, l#0, p#0);
        }

        if (_module.__default.Inv(_module._default.Index$A, l#0)
           && _module.__default.MaybePtr(_module._default.Index$A, l#0, p#0))
        {
            assume _module.DList.DList_q(l#0);
            assert 0 <= p#0 && p#0 < Seq#Length(_module.DList.g(l#0));
            assume _module.__default.Index(_module._default.Index$A, l#0, p#0)
               == $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int;
            assume _module.DList.DList_q(l#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Index(_module._default.Index$A, l#0, p#0), TInt);
        }
        else
        {
            assume _module.__default.Index(_module._default.Index$A, l#0, p#0) == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Index(_module._default.Index$A, l#0, p#0), TInt);
        }

        assume _module.__default.Index(_module._default.Index$A, l#0, p#0) == i#0;
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.IndexHi
function _module.__default.IndexHi(_module._default.IndexHi$A: Ty, l#0: DatatypeType, p#0: int) : int;

function _module.__default.IndexHi#canCall(_module._default.IndexHi$A: Ty, l#0: DatatypeType, p#0: int) : bool;

// consequence axiom for _module.__default.IndexHi
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.IndexHi$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0) } 
    _module.__default.IndexHi#canCall(_module._default.IndexHi$A, l#0, p#0)
         || (17 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.IndexHi$A)))
       ==> (_module.__default.Inv(_module._default.IndexHi$A, l#0)
             && _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0)
           ==> _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0)
             == _module.__default.Index(_module._default.IndexHi$A, l#0, p#0))
         && (_module.__default.Inv(_module._default.IndexHi$A, l#0) && p#0 == LitInt(0)
           ==> _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0)
             == Seq#Length(_module.__default.Seq(_module._default.IndexHi$A, l#0))));

function _module.__default.IndexHi#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.__default.IndexHi
axiom (forall _module._default.IndexHi$A: Ty, l#0: DatatypeType, p#0: int :: 
  { _module.__default.IndexHi#requires(_module._default.IndexHi$A, l#0, p#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.IndexHi$A))
     ==> _module.__default.IndexHi#requires(_module._default.IndexHi$A, l#0, p#0) == true);

// definition axiom for _module.__default.IndexHi (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.IndexHi$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0) } 
    _module.__default.IndexHi#canCall(_module._default.IndexHi$A, l#0, p#0)
         || (17 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.IndexHi$A)))
       ==> _module.__default.Inv#canCall(_module._default.IndexHi$A, l#0)
         && (_module.__default.Inv(_module._default.IndexHi$A, l#0)
           ==> _module.__default.ValidPtr#canCall(_module._default.IndexHi$A, l#0, p#0))
         && (_module.__default.Inv(_module._default.IndexHi$A, l#0)
             && _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0)
           ==> _module.DList.DList_q(l#0))
         && (!(_module.__default.Inv(_module._default.IndexHi$A, l#0)
             && _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0))
           ==> _module.DList.DList_q(l#0))
         && _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0)
           == (if _module.__default.Inv(_module._default.IndexHi$A, l#0)
               && _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0)
             then $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int
             else Seq#Length(_module.DList.s(l#0))));

// definition axiom for _module.__default.IndexHi for all literals (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.IndexHi$A: Ty, l#0: DatatypeType, p#0: int :: 
    {:weight 3} { _module.__default.IndexHi(_module._default.IndexHi$A, Lit(l#0), LitInt(p#0)) } 
    _module.__default.IndexHi#canCall(_module._default.IndexHi$A, Lit(l#0), LitInt(p#0))
         || (17 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.DList(_module._default.IndexHi$A)))
       ==> _module.__default.Inv#canCall(_module._default.IndexHi$A, Lit(l#0))
         && (Lit(_module.__default.Inv(_module._default.IndexHi$A, Lit(l#0)))
           ==> _module.__default.ValidPtr#canCall(_module._default.IndexHi$A, Lit(l#0), LitInt(p#0)))
         && (Lit(_module.__default.Inv(_module._default.IndexHi$A, Lit(l#0))
               && _module.__default.ValidPtr(_module._default.IndexHi$A, Lit(l#0), LitInt(p#0)))
           ==> _module.DList.DList_q(Lit(l#0)))
         && (!Lit(_module.__default.Inv(_module._default.IndexHi$A, Lit(l#0))
               && _module.__default.ValidPtr(_module._default.IndexHi$A, Lit(l#0), LitInt(p#0)))
           ==> _module.DList.DList_q(Lit(l#0)))
         && _module.__default.IndexHi(_module._default.IndexHi$A, Lit(l#0), LitInt(p#0))
           == (if _module.__default.Inv(_module._default.IndexHi$A, Lit(l#0))
               && _module.__default.ValidPtr(_module._default.IndexHi$A, Lit(l#0), LitInt(p#0))
             then $Unbox(Seq#Index(Lit(_module.DList.g(Lit(l#0))), LitInt(p#0))): int
             else Seq#Length(Lit(_module.DList.s(Lit(l#0))))));

procedure CheckWellformed$$_module.__default.IndexHi(_module._default.IndexHi$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.IndexHi$A)), 
    p#0: int)
   returns (i#0: int);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.Inv(_module._default.IndexHi$A, l#0)
       && _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0)
     ==> i#0 == _module.__default.Index(_module._default.IndexHi$A, l#0, p#0);
  ensures _module.__default.Inv(_module._default.IndexHi$A, l#0) && p#0 == LitInt(0)
     ==> i#0 == Seq#Length(_module.__default.Seq(_module._default.IndexHi$A, l#0));



implementation CheckWellformed$$_module.__default.IndexHi(_module._default.IndexHi$A: Ty, l#0: DatatypeType, p#0: int) returns (i#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var ##l#2: DatatypeType;
  var ##p#1: int;
  var ##l#3: DatatypeType;
  var ##l#4: DatatypeType;
  var ##l#5: DatatypeType;
  var ##l#6: DatatypeType;
  var ##p#2: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function IndexHi
    assume {:captureState "DLL_Dafny.dfy(149,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (*)
        {
            ##l#0 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.IndexHi$A), $Heap);
            assume _module.__default.Inv#canCall(_module._default.IndexHi$A, l#0);
            assume _module.__default.Inv(_module._default.IndexHi$A, l#0);
            ##l#1 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.IndexHi$A), $Heap);
            ##p#0 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#0, TInt, $Heap);
            assume _module.__default.ValidPtr#canCall(_module._default.IndexHi$A, l#0, p#0);
            assume _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0);
            ##l#2 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.IndexHi$A), $Heap);
            ##p#1 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#1, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.IndexHi$A, l#0, p#0);
            assume i#0 == _module.__default.Index(_module._default.IndexHi$A, l#0, p#0);
        }
        else
        {
            assume _module.__default.Inv(_module._default.IndexHi$A, l#0)
                 && _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0)
               ==> i#0 == _module.__default.Index(_module._default.IndexHi$A, l#0, p#0);
        }

        if (*)
        {
            ##l#3 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.IndexHi$A), $Heap);
            assume _module.__default.Inv#canCall(_module._default.IndexHi$A, l#0);
            assume _module.__default.Inv(_module._default.IndexHi$A, l#0);
            assume p#0 == LitInt(0);
            ##l#4 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#4, Tclass._module.DList(_module._default.IndexHi$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.IndexHi$A, l#0);
            assume i#0 == Seq#Length(_module.__default.Seq(_module._default.IndexHi$A, l#0));
        }
        else
        {
            assume _module.__default.Inv(_module._default.IndexHi$A, l#0) && p#0 == LitInt(0)
               ==> i#0 == Seq#Length(_module.__default.Seq(_module._default.IndexHi$A, l#0));
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##l#5 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#5, Tclass._module.DList(_module._default.IndexHi$A), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Inv#canCall(_module._default.IndexHi$A, l#0);
        if (_module.__default.Inv(_module._default.IndexHi$A, l#0))
        {
            ##l#6 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#6, Tclass._module.DList(_module._default.IndexHi$A), $Heap);
            ##p#2 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#2, TInt, $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.ValidPtr#canCall(_module._default.IndexHi$A, l#0, p#0);
        }

        if (_module.__default.Inv(_module._default.IndexHi$A, l#0)
           && _module.__default.ValidPtr(_module._default.IndexHi$A, l#0, p#0))
        {
            assume _module.DList.DList_q(l#0);
            assert 0 <= p#0 && p#0 < Seq#Length(_module.DList.g(l#0));
            assume _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0)
               == $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int;
            assume _module.DList.DList_q(l#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0), TInt);
        }
        else
        {
            assume _module.DList.DList_q(l#0);
            assume _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0)
               == Seq#Length(_module.DList.s(l#0));
            assume _module.DList.DList_q(l#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0), TInt);
        }

        assume _module.__default.IndexHi(_module._default.IndexHi$A, l#0, p#0) == i#0;
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.Get
function _module.__default.Get(_module._default.Get$A: Ty, l#0: DatatypeType, p#0: int) : Box;

function _module.__default.Get#canCall(_module._default.Get$A: Ty, l#0: DatatypeType, p#0: int) : bool;

// consequence axiom for _module.__default.Get
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Get$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Get(_module._default.Get$A, l#0, p#0) } 
    _module.__default.Get#canCall(_module._default.Get$A, l#0, p#0)
         || (19 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Get$A))
           && 
          _module.__default.Inv(_module._default.Get$A, l#0)
           && _module.__default.ValidPtr(_module._default.Get$A, l#0, p#0))
       ==> _module.__default.Get(_module._default.Get$A, l#0, p#0)
           == Seq#Index(_module.__default.Seq(_module._default.Get$A, l#0), 
            _module.__default.Index(_module._default.Get$A, l#0, p#0))
         && $IsBox(_module.__default.Get(_module._default.Get$A, l#0, p#0), _module._default.Get$A));

function _module.__default.Get#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.__default.Get
axiom (forall _module._default.Get$A: Ty, l#0: DatatypeType, p#0: int :: 
  { _module.__default.Get#requires(_module._default.Get$A, l#0, p#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.Get$A))
     ==> _module.__default.Get#requires(_module._default.Get$A, l#0, p#0)
       == (_module.__default.Inv(_module._default.Get$A, l#0)
         && _module.__default.ValidPtr(_module._default.Get$A, l#0, p#0)));

// definition axiom for _module.__default.Get (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Get$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Get(_module._default.Get$A, l#0, p#0) } 
    _module.__default.Get#canCall(_module._default.Get$A, l#0, p#0)
         || (19 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Get$A))
           && 
          _module.__default.Inv(_module._default.Get$A, l#0)
           && _module.__default.ValidPtr(_module._default.Get$A, l#0, p#0))
       ==> _module.DList.DList_q(l#0)
         && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)
         && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)): DatatypeType)
         && _module.__default.Get(_module._default.Get$A, l#0, p#0)
           == _module.Option.value(_module.Node.data($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)): DatatypeType)));

// definition axiom for _module.__default.Get for all literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Get$A: Ty, l#0: DatatypeType, p#0: int :: 
    {:weight 3} { _module.__default.Get(_module._default.Get$A, Lit(l#0), LitInt(p#0)) } 
    _module.__default.Get#canCall(_module._default.Get$A, Lit(l#0), LitInt(p#0))
         || (19 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Get$A))
           && 
          Lit(_module.__default.Inv(_module._default.Get$A, Lit(l#0)))
           && Lit(_module.__default.ValidPtr(_module._default.Get$A, Lit(l#0), LitInt(p#0))))
       ==> _module.DList.DList_q(Lit(l#0))
         && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Get$A), 
          Lit(_module.DList.nodes(Lit(l#0))), 
          LitInt(p#0))
         && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), 
              Lit(_module.DList.nodes(Lit(l#0))), 
              LitInt(p#0))): DatatypeType)
         && _module.__default.Get(_module._default.Get$A, Lit(l#0), LitInt(p#0))
           == _module.Option.value(_module.Node.data($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), 
                  Lit(_module.DList.nodes(Lit(l#0))), 
                  LitInt(p#0))): DatatypeType)));

procedure CheckWellformed$$_module.__default.Get(_module._default.Get$A: Ty, 
    l#0: DatatypeType where $Is(l#0, Tclass._module.DList(_module._default.Get$A)), 
    p#0: int)
   returns (a#0: Box where $IsBox(a#0, _module._default.Get$A));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures a#0
     == Seq#Index(_module.__default.Seq(_module._default.Get$A, l#0), 
      _module.__default.Index(_module._default.Get$A, l#0, p#0));



implementation CheckWellformed$$_module.__default.Get(_module._default.Get$A: Ty, l#0: DatatypeType, p#0: int) returns (a#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##l#2: DatatypeType;
  var ##l#3: DatatypeType;
  var ##p#1: int;
  var ##s#0: Seq Box;
  var ##i#0: int;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Get
    assume {:captureState "DLL_Dafny.dfy(156,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.Get$A), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.Inv#canCall(_module._default.Get$A, l#0);
    assume _module.__default.Inv(_module._default.Get$A, l#0);
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.Get$A), $Heap);
    ##p#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#0, TInt, $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.ValidPtr#canCall(_module._default.Get$A, l#0, p#0);
    assume _module.__default.ValidPtr(_module._default.Get$A, l#0, p#0);
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $IsBox(_module.__default.Get(_module._default.Get$A, l#0, p#0), _module._default.Get$A);
        ##l#2 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.Get$A), $Heap);
        assume _module.__default.Seq#canCall(_module._default.Get$A, l#0);
        ##l#3 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.Get$A), $Heap);
        ##p#1 := p#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#1, TInt, $Heap);
        assume _module.__default.Index#canCall(_module._default.Get$A, l#0, p#0);
        assert 0 <= _module.__default.Index(_module._default.Get$A, l#0, p#0)
           && _module.__default.Index(_module._default.Get$A, l#0, p#0)
             < Seq#Length(_module.__default.Seq(_module._default.Get$A, l#0));
        assume a#0
           == Seq#Index(_module.__default.Seq(_module._default.Get$A, l#0), 
            _module.__default.Index(_module._default.Get$A, l#0, p#0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.DList.DList_q(l#0);
        ##s#0 := _module.DList.nodes(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, TSeq(Tclass._module.Node(_module._default.Get$A)), $Heap);
        ##i#0 := p#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#0, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#0;
        assert {:subsumption 0} ##i#0 < Seq#Length(##s#0);
        assume LitInt(0) <= ##i#0 && ##i#0 < Seq#Length(##s#0);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assert _module.Option.Some_q(_module.Node.data($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)): DatatypeType));
        assume _module.__default.Get(_module._default.Get$A, l#0, p#0)
           == _module.Option.value(_module.Node.data($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)): DatatypeType));
        assume _module.DList.DList_q(l#0)
           && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)
           && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Get$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        // CheckWellformedWithResult: any expression
        assume $IsBox(_module.__default.Get(_module._default.Get$A, l#0, p#0), _module._default.Get$A);
        assume _module.__default.Get(_module._default.Get$A, l#0, p#0) == a#0;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.Next
function _module.__default.Next(_module._default.Next$A: Ty, l#0: DatatypeType, p#0: int) : int;

function _module.__default.Next#canCall(_module._default.Next$A: Ty, l#0: DatatypeType, p#0: int) : bool;

// consequence axiom for _module.__default.Next
axiom 20 <= $FunctionContextHeight
   ==> (forall _module._default.Next$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Next(_module._default.Next$A, l#0, p#0) } 
    _module.__default.Next#canCall(_module._default.Next$A, l#0, p#0)
         || (20 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Next$A))
           && 
          _module.__default.Inv(_module._default.Next$A, l#0)
           && _module.__default.MaybePtr(_module._default.Next$A, l#0, p#0))
       ==> _module.__default.MaybePtr(_module._default.Next$A, 
          l#0, 
          _module.__default.Next(_module._default.Next$A, l#0, p#0))
         && (p#0 == LitInt(0)
             && Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) > 0
           ==> _module.__default.Index(_module._default.Next$A, 
              l#0, 
              _module.__default.Next(_module._default.Next$A, l#0, p#0))
             == LitInt(0))
         && (p#0 == LitInt(0)
             && Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) == LitInt(0)
           ==> _module.__default.Next(_module._default.Next$A, l#0, p#0) == LitInt(0))
         && (p#0 != 0
             && _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
               < Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0))
           ==> _module.__default.Index(_module._default.Next$A, 
              l#0, 
              _module.__default.Next(_module._default.Next$A, l#0, p#0))
             == _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1)))
         && (p#0 != 0
             && _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
               == Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0))
           ==> _module.__default.Next(_module._default.Next$A, l#0, p#0) == LitInt(0)));

function _module.__default.Next#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.__default.Next
axiom (forall _module._default.Next$A: Ty, l#0: DatatypeType, p#0: int :: 
  { _module.__default.Next#requires(_module._default.Next$A, l#0, p#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.Next$A))
     ==> _module.__default.Next#requires(_module._default.Next$A, l#0, p#0)
       == (_module.__default.Inv(_module._default.Next$A, l#0)
         && _module.__default.MaybePtr(_module._default.Next$A, l#0, p#0)));

// definition axiom for _module.__default.Next (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall _module._default.Next$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Next(_module._default.Next$A, l#0, p#0) } 
    _module.__default.Next#canCall(_module._default.Next$A, l#0, p#0)
         || (20 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Next$A))
           && 
          _module.__default.Inv(_module._default.Next$A, l#0)
           && _module.__default.MaybePtr(_module._default.Next$A, l#0, p#0))
       ==> _module.DList.DList_q(l#0)
         && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)
         && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)): DatatypeType)
         && _module.__default.Next(_module._default.Next$A, l#0, p#0)
           == _module.Node.next($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)): DatatypeType));

// definition axiom for _module.__default.Next for all literals (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall _module._default.Next$A: Ty, l#0: DatatypeType, p#0: int :: 
    {:weight 3} { _module.__default.Next(_module._default.Next$A, Lit(l#0), LitInt(p#0)) } 
    _module.__default.Next#canCall(_module._default.Next$A, Lit(l#0), LitInt(p#0))
         || (20 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Next$A))
           && 
          Lit(_module.__default.Inv(_module._default.Next$A, Lit(l#0)))
           && Lit(_module.__default.MaybePtr(_module._default.Next$A, Lit(l#0), LitInt(p#0))))
       ==> _module.DList.DList_q(Lit(l#0))
         && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Next$A), 
          Lit(_module.DList.nodes(Lit(l#0))), 
          LitInt(p#0))
         && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), 
              Lit(_module.DList.nodes(Lit(l#0))), 
              LitInt(p#0))): DatatypeType)
         && _module.__default.Next(_module._default.Next$A, Lit(l#0), LitInt(p#0))
           == _module.Node.next($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), 
                Lit(_module.DList.nodes(Lit(l#0))), 
                LitInt(p#0))): DatatypeType));

procedure CheckWellformed$$_module.__default.Next(_module._default.Next$A: Ty, 
    l#0: DatatypeType where $Is(l#0, Tclass._module.DList(_module._default.Next$A)), 
    p#0: int)
   returns (p'#0: int);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.MaybePtr#canCall(_module._default.Next$A, l#0, p'#0)
     ==> _module.__default.MaybePtr(_module._default.Next$A, l#0, p'#0)
       || 
      p'#0 == LitInt(0)
       || _module.__default.ValidPtr(_module._default.Next$A, l#0, p'#0);
  ensures p#0 == LitInt(0)
       && Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) > 0
     ==> _module.__default.Index(_module._default.Next$A, l#0, p'#0) == LitInt(0);
  ensures p#0 == LitInt(0)
       && Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) == LitInt(0)
     ==> p'#0 == LitInt(0);
  ensures p#0 != 0
       && _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
         < Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0))
     ==> _module.__default.Index(_module._default.Next$A, l#0, p'#0)
       == _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1));
  ensures p#0 != 0
       && _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
         == Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0))
     ==> p'#0 == LitInt(0);



implementation CheckWellformed$$_module.__default.Next(_module._default.Next$A: Ty, l#0: DatatypeType, p#0: int) returns (p'#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##l#2: DatatypeType;
  var ##p#1: int;
  var ##l#3: DatatypeType;
  var ##l#4: DatatypeType;
  var ##p#2: int;
  var ##l#5: DatatypeType;
  var ##l#6: DatatypeType;
  var ##p#3: int;
  var ##a#0: int;
  var ##b#0: int;
  var ##l#7: DatatypeType;
  var ##l#8: DatatypeType;
  var ##p#4: int;
  var ##l#9: DatatypeType;
  var ##p#5: int;
  var ##a#1: int;
  var ##b#1: int;
  var ##l#10: DatatypeType;
  var ##p#6: int;
  var ##a#2: int;
  var ##b#2: int;
  var ##l#11: DatatypeType;
  var ##s#0: Seq Box;
  var ##i#0: int;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Next
    assume {:captureState "DLL_Dafny.dfy(164,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.Next$A), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.Inv#canCall(_module._default.Next$A, l#0);
    assume _module.__default.Inv(_module._default.Next$A, l#0);
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.Next$A), $Heap);
    ##p#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#0, TInt, $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.MaybePtr#canCall(_module._default.Next$A, l#0, p#0);
    assume _module.__default.MaybePtr(_module._default.Next$A, l#0, p#0);
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        ##l#2 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.Next$A), $Heap);
        ##p#1 := p'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#1, TInt, $Heap);
        assume _module.__default.MaybePtr#canCall(_module._default.Next$A, l#0, p'#0);
        assume _module.__default.MaybePtr(_module._default.Next$A, l#0, p'#0);
        if (*)
        {
            assume p#0 == LitInt(0);
            ##l#3 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.Next$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.Next$A, l#0);
            assume Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) > 0;
            ##l#4 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#4, Tclass._module.DList(_module._default.Next$A), $Heap);
            ##p#2 := p'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#2, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Next$A, l#0, p'#0);
            assume _module.__default.Index(_module._default.Next$A, l#0, p'#0) == LitInt(0);
        }
        else
        {
            assume p#0 == LitInt(0)
                 && Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) > 0
               ==> _module.__default.Index(_module._default.Next$A, l#0, p'#0) == LitInt(0);
        }

        if (*)
        {
            assume p#0 == LitInt(0);
            ##l#5 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#5, Tclass._module.DList(_module._default.Next$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.Next$A, l#0);
            assume Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) == LitInt(0);
            assume p'#0 == LitInt(0);
        }
        else
        {
            assume p#0 == LitInt(0)
                 && Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0)) == LitInt(0)
               ==> p'#0 == LitInt(0);
        }

        if (*)
        {
            assume p#0 != 0;
            ##l#6 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#6, Tclass._module.DList(_module._default.Next$A), $Heap);
            ##p#3 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#3, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Next$A, l#0, p#0);
            ##a#0 := _module.__default.Index(_module._default.Next$A, l#0, p#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, TInt, $Heap);
            ##b#0 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assume _module.__default.Add#canCall(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1));
            ##l#7 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#7, Tclass._module.DList(_module._default.Next$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.Next$A, l#0);
            assume _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
               < Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0));
            ##l#8 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#8, Tclass._module.DList(_module._default.Next$A), $Heap);
            ##p#4 := p'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#4, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Next$A, l#0, p'#0);
            ##l#9 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#9, Tclass._module.DList(_module._default.Next$A), $Heap);
            ##p#5 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#5, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Next$A, l#0, p#0);
            ##a#1 := _module.__default.Index(_module._default.Next$A, l#0, p#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            ##b#1 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assume _module.__default.Add#canCall(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1));
            assume _module.__default.Index(_module._default.Next$A, l#0, p'#0)
               == _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1));
        }
        else
        {
            assume p#0 != 0
                 && _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
                   < Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0))
               ==> _module.__default.Index(_module._default.Next$A, l#0, p'#0)
                 == _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1));
        }

        if (*)
        {
            assume p#0 != 0;
            ##l#10 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#10, Tclass._module.DList(_module._default.Next$A), $Heap);
            ##p#6 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#6, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Next$A, l#0, p#0);
            ##a#2 := _module.__default.Index(_module._default.Next$A, l#0, p#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#2, TInt, $Heap);
            ##b#2 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assume _module.__default.Add#canCall(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1));
            ##l#11 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#11, Tclass._module.DList(_module._default.Next$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.Next$A, l#0);
            assume _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
               == Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0));
            assume p'#0 == LitInt(0);
        }
        else
        {
            assume p#0 != 0
                 && _module.__default.Add(_module.__default.Index(_module._default.Next$A, l#0, p#0), LitInt(1))
                   == Seq#Length(_module.__default.Seq(_module._default.Next$A, l#0))
               ==> p'#0 == LitInt(0);
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.DList.DList_q(l#0);
        ##s#0 := _module.DList.nodes(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, TSeq(Tclass._module.Node(_module._default.Next$A)), $Heap);
        ##i#0 := p#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#0, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#0;
        assert {:subsumption 0} ##i#0 < Seq#Length(##s#0);
        assume LitInt(0) <= ##i#0 && ##i#0 < Seq#Length(##s#0);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assume _module.__default.Next(_module._default.Next$A, l#0, p#0)
           == _module.Node.next($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assume _module.DList.DList_q(l#0)
           && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)
           && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Next$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Next(_module._default.Next$A, l#0, p#0), TInt);
        assume _module.__default.Next(_module._default.Next$A, l#0, p#0) == p'#0;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.Prev
function _module.__default.Prev(_module._default.Prev$A: Ty, l#0: DatatypeType, p#0: int) : int;

function _module.__default.Prev#canCall(_module._default.Prev$A: Ty, l#0: DatatypeType, p#0: int) : bool;

// consequence axiom for _module.__default.Prev
axiom 21 <= $FunctionContextHeight
   ==> (forall _module._default.Prev$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Prev(_module._default.Prev$A, l#0, p#0) } 
    _module.__default.Prev#canCall(_module._default.Prev$A, l#0, p#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Prev$A))
           && 
          _module.__default.Inv(_module._default.Prev$A, l#0)
           && _module.__default.MaybePtr(_module._default.Prev$A, l#0, p#0))
       ==> _module.__default.MaybePtr(_module._default.Prev$A, 
          l#0, 
          _module.__default.Prev(_module._default.Prev$A, l#0, p#0))
         && (p#0 == LitInt(0)
             && Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) > 0
           ==> _module.__default.Index(_module._default.Prev$A, 
              l#0, 
              _module.__default.Prev(_module._default.Prev$A, l#0, p#0))
             == _module.__default.Sub(Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)), LitInt(1)))
         && (p#0 == LitInt(0)
             && Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) == LitInt(0)
           ==> _module.__default.Prev(_module._default.Prev$A, l#0, p#0) == LitInt(0))
         && (p#0 != 0 && _module.__default.Index(_module._default.Prev$A, l#0, p#0) > 0
           ==> _module.__default.Index(_module._default.Prev$A, 
              l#0, 
              _module.__default.Prev(_module._default.Prev$A, l#0, p#0))
             == _module.__default.Sub(_module.__default.Index(_module._default.Prev$A, l#0, p#0), LitInt(1)))
         && (p#0 != 0
             && 
            _module.__default.Index(_module._default.Prev$A, l#0, p#0) == LitInt(0)
             && LitInt(0) == Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0))
           ==> _module.__default.Prev(_module._default.Prev$A, l#0, p#0) == LitInt(0)));

function _module.__default.Prev#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.__default.Prev
axiom (forall _module._default.Prev$A: Ty, l#0: DatatypeType, p#0: int :: 
  { _module.__default.Prev#requires(_module._default.Prev$A, l#0, p#0) } 
  $Is(l#0, Tclass._module.DList(_module._default.Prev$A))
     ==> _module.__default.Prev#requires(_module._default.Prev$A, l#0, p#0)
       == (_module.__default.Inv(_module._default.Prev$A, l#0)
         && _module.__default.MaybePtr(_module._default.Prev$A, l#0, p#0)));

// definition axiom for _module.__default.Prev (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall _module._default.Prev$A: Ty, l#0: DatatypeType, p#0: int :: 
    { _module.__default.Prev(_module._default.Prev$A, l#0, p#0) } 
    _module.__default.Prev#canCall(_module._default.Prev$A, l#0, p#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Prev$A))
           && 
          _module.__default.Inv(_module._default.Prev$A, l#0)
           && _module.__default.MaybePtr(_module._default.Prev$A, l#0, p#0))
       ==> _module.DList.DList_q(l#0)
         && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)
         && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)): DatatypeType)
         && _module.__default.Prev(_module._default.Prev$A, l#0, p#0)
           == _module.Node.prev($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)): DatatypeType));

// definition axiom for _module.__default.Prev for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall _module._default.Prev$A: Ty, l#0: DatatypeType, p#0: int :: 
    {:weight 3} { _module.__default.Prev(_module._default.Prev$A, Lit(l#0), LitInt(p#0)) } 
    _module.__default.Prev#canCall(_module._default.Prev$A, Lit(l#0), LitInt(p#0))
         || (21 != $FunctionContextHeight
           && 
          $Is(l#0, Tclass._module.DList(_module._default.Prev$A))
           && 
          Lit(_module.__default.Inv(_module._default.Prev$A, Lit(l#0)))
           && Lit(_module.__default.MaybePtr(_module._default.Prev$A, Lit(l#0), LitInt(p#0))))
       ==> _module.DList.DList_q(Lit(l#0))
         && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Prev$A), 
          Lit(_module.DList.nodes(Lit(l#0))), 
          LitInt(p#0))
         && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), 
              Lit(_module.DList.nodes(Lit(l#0))), 
              LitInt(p#0))): DatatypeType)
         && _module.__default.Prev(_module._default.Prev$A, Lit(l#0), LitInt(p#0))
           == _module.Node.prev($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), 
                Lit(_module.DList.nodes(Lit(l#0))), 
                LitInt(p#0))): DatatypeType));

procedure CheckWellformed$$_module.__default.Prev(_module._default.Prev$A: Ty, 
    l#0: DatatypeType where $Is(l#0, Tclass._module.DList(_module._default.Prev$A)), 
    p#0: int)
   returns (p'#0: int);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.MaybePtr#canCall(_module._default.Prev$A, l#0, p'#0)
     ==> _module.__default.MaybePtr(_module._default.Prev$A, l#0, p'#0)
       || 
      p'#0 == LitInt(0)
       || _module.__default.ValidPtr(_module._default.Prev$A, l#0, p'#0);
  ensures p#0 == LitInt(0)
       && Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) > 0
     ==> _module.__default.Index(_module._default.Prev$A, l#0, p'#0)
       == _module.__default.Sub(Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)), LitInt(1));
  ensures p#0 == LitInt(0)
       && Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) == LitInt(0)
     ==> p'#0 == LitInt(0);
  ensures p#0 != 0 && _module.__default.Index(_module._default.Prev$A, l#0, p#0) > 0
     ==> _module.__default.Index(_module._default.Prev$A, l#0, p'#0)
       == _module.__default.Sub(_module.__default.Index(_module._default.Prev$A, l#0, p#0), LitInt(1));
  ensures p#0 != 0
       && 
      _module.__default.Index(_module._default.Prev$A, l#0, p#0) == LitInt(0)
       && LitInt(0) == Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0))
     ==> p'#0 == LitInt(0);



implementation CheckWellformed$$_module.__default.Prev(_module._default.Prev$A: Ty, l#0: DatatypeType, p#0: int) returns (p'#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##l#2: DatatypeType;
  var ##p#1: int;
  var ##l#3: DatatypeType;
  var ##l#4: DatatypeType;
  var ##p#2: int;
  var ##l#5: DatatypeType;
  var ##a#0: int;
  var ##b#0: int;
  var ##l#6: DatatypeType;
  var ##l#7: DatatypeType;
  var ##p#3: int;
  var ##l#8: DatatypeType;
  var ##p#4: int;
  var ##l#9: DatatypeType;
  var ##p#5: int;
  var ##a#1: int;
  var ##b#1: int;
  var ##l#10: DatatypeType;
  var ##p#6: int;
  var ##l#11: DatatypeType;
  var ##s#0: Seq Box;
  var ##i#0: int;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Prev
    assume {:captureState "DLL_Dafny.dfy(176,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.Prev$A), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.Inv#canCall(_module._default.Prev$A, l#0);
    assume _module.__default.Inv(_module._default.Prev$A, l#0);
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.Prev$A), $Heap);
    ##p#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#0, TInt, $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.MaybePtr#canCall(_module._default.Prev$A, l#0, p#0);
    assume _module.__default.MaybePtr(_module._default.Prev$A, l#0, p#0);
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        ##l#2 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.Prev$A), $Heap);
        ##p#1 := p'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#1, TInt, $Heap);
        assume _module.__default.MaybePtr#canCall(_module._default.Prev$A, l#0, p'#0);
        assume _module.__default.MaybePtr(_module._default.Prev$A, l#0, p'#0);
        if (*)
        {
            assume p#0 == LitInt(0);
            ##l#3 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.Prev$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.Prev$A, l#0);
            assume Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) > 0;
            ##l#4 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#4, Tclass._module.DList(_module._default.Prev$A), $Heap);
            ##p#2 := p'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#2, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Prev$A, l#0, p'#0);
            ##l#5 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#5, Tclass._module.DList(_module._default.Prev$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.Prev$A, l#0);
            ##a#0 := Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, TInt, $Heap);
            ##b#0 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assume _module.__default.Sub#canCall(Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)), LitInt(1));
            assume _module.__default.Index(_module._default.Prev$A, l#0, p'#0)
               == _module.__default.Sub(Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)), LitInt(1));
        }
        else
        {
            assume p#0 == LitInt(0)
                 && Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) > 0
               ==> _module.__default.Index(_module._default.Prev$A, l#0, p'#0)
                 == _module.__default.Sub(Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)), LitInt(1));
        }

        if (*)
        {
            assume p#0 == LitInt(0);
            ##l#6 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#6, Tclass._module.DList(_module._default.Prev$A), $Heap);
            assume _module.__default.Seq#canCall(_module._default.Prev$A, l#0);
            assume Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) == LitInt(0);
            assume p'#0 == LitInt(0);
        }
        else
        {
            assume p#0 == LitInt(0)
                 && Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0)) == LitInt(0)
               ==> p'#0 == LitInt(0);
        }

        if (*)
        {
            assume p#0 != 0;
            ##l#7 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#7, Tclass._module.DList(_module._default.Prev$A), $Heap);
            ##p#3 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#3, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Prev$A, l#0, p#0);
            assume _module.__default.Index(_module._default.Prev$A, l#0, p#0) > 0;
            ##l#8 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#8, Tclass._module.DList(_module._default.Prev$A), $Heap);
            ##p#4 := p'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#4, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Prev$A, l#0, p'#0);
            ##l#9 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#9, Tclass._module.DList(_module._default.Prev$A), $Heap);
            ##p#5 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#5, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Prev$A, l#0, p#0);
            ##a#1 := _module.__default.Index(_module._default.Prev$A, l#0, p#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, TInt, $Heap);
            ##b#1 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assume _module.__default.Sub#canCall(_module.__default.Index(_module._default.Prev$A, l#0, p#0), LitInt(1));
            assume _module.__default.Index(_module._default.Prev$A, l#0, p'#0)
               == _module.__default.Sub(_module.__default.Index(_module._default.Prev$A, l#0, p#0), LitInt(1));
        }
        else
        {
            assume p#0 != 0 && _module.__default.Index(_module._default.Prev$A, l#0, p#0) > 0
               ==> _module.__default.Index(_module._default.Prev$A, l#0, p'#0)
                 == _module.__default.Sub(_module.__default.Index(_module._default.Prev$A, l#0, p#0), LitInt(1));
        }

        if (*)
        {
            assume p#0 != 0;
            ##l#10 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#10, Tclass._module.DList(_module._default.Prev$A), $Heap);
            ##p#6 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#6, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Prev$A, l#0, p#0);
            if (_module.__default.Index(_module._default.Prev$A, l#0, p#0) == LitInt(0))
            {
                ##l#11 := l#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##l#11, Tclass._module.DList(_module._default.Prev$A), $Heap);
                assume _module.__default.Seq#canCall(_module._default.Prev$A, l#0);
            }

            assume _module.__default.Index(_module._default.Prev$A, l#0, p#0) == LitInt(0)
               && LitInt(0) == Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0));
            assume p'#0 == LitInt(0);
        }
        else
        {
            assume p#0 != 0
                 && 
                _module.__default.Index(_module._default.Prev$A, l#0, p#0) == LitInt(0)
                 && LitInt(0) == Seq#Length(_module.__default.Seq(_module._default.Prev$A, l#0))
               ==> p'#0 == LitInt(0);
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.DList.DList_q(l#0);
        ##s#0 := _module.DList.nodes(l#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, TSeq(Tclass._module.Node(_module._default.Prev$A)), $Heap);
        ##i#0 := p#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#0, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#0;
        assert {:subsumption 0} ##i#0 < Seq#Length(##s#0);
        assume LitInt(0) <= ##i#0 && ##i#0 < Seq#Length(##s#0);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assume _module.__default.Prev(_module._default.Prev$A, l#0, p#0)
           == _module.Node.prev($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        assume _module.DList.DList_q(l#0)
           && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)
           && _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Prev$A), _module.DList.nodes(l#0), p#0)): DatatypeType);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Prev(_module._default.Prev$A, l#0, p#0), TInt);
        assume _module.__default.Prev(_module._default.Prev$A, l#0, p#0) == p'#0;
        assert b$reqreads#2;
    }
}



procedure CheckWellformed$$_module.__default.BuildFreeStack(_module._default.BuildFreeStack$A: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)))
         && $IsAlloc(a#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap), 
    k#0: int)
   returns (b#0: Seq Box
       where $Is(b#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)))
         && $IsAlloc(b#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.BuildFreeStack(_module._default.BuildFreeStack$A: Ty, a#0: Seq Box, k#0: int)
   returns (b#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var i#2: int;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: BuildFreeStack, CheckWellformed$$_module.__default.BuildFreeStack
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(188,7): initial state"} true;
    if (0 < k#0)
    {
    }

    assume 0 < k#0 && k#0 <= Seq#Length(a#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc b#0;
    assume {:captureState "DLL_Dafny.dfy(190,14): post-state"} true;
    assume Seq#Length(b#0) == Seq#Length(a#0);
    havoc i#0;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assume i#0 < k#0;
        assert 0 <= i#0 && i#0 < Seq#Length(b#0);
        assert 0 <= i#0 && i#0 < Seq#Length(a#0);
        assume _module.Node#Equal($Unbox(Seq#Index(b#0, i#0)): DatatypeType, 
          $Unbox(Seq#Index(a#0, i#0)): DatatypeType);
    }
    else
    {
        assume LitInt(0) <= i#0 && i#0 < k#0
           ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#0)): DatatypeType, 
            $Unbox(Seq#Index(a#0, i#0)): DatatypeType);
    }

    assume (forall i#1: int :: 
      { $Unbox(Seq#Index(a#0, i#1)): DatatypeType } 
        { $Unbox(Seq#Index(b#0, i#1)): DatatypeType } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 < k#0
         ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#1)): DatatypeType, 
          $Unbox(Seq#Index(a#0, i#1)): DatatypeType));
    havoc i#2;
    if (*)
    {
        assume k#0 <= i#2;
        assume i#2 < Seq#Length(a#0);
        assert 0 <= i#2 && i#2 < Seq#Length(b#0);
        ##a#0 := i#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, TInt, $Heap);
        ##b#0 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, TInt, $Heap);
        assume _module.__default.Sub#canCall(i#2, LitInt(1));
        assume _module.Node#Equal($Unbox(Seq#Index(b#0, i#2)): DatatypeType, 
          #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(i#2, LitInt(1)), LitInt(0)));
    }
    else
    {
        assume k#0 <= i#2 && i#2 < Seq#Length(a#0)
           ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#2)): DatatypeType, 
            #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(i#2, LitInt(1)), LitInt(0)));
    }

    assume (forall i#3: int :: 
      { _module.__default.Sub(i#3, 1) } { $Unbox(Seq#Index(b#0, i#3)): DatatypeType } 
      true
         ==> 
        k#0 <= i#3 && i#3 < Seq#Length(a#0)
         ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#3)): DatatypeType, 
          #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(i#3, LitInt(1)), LitInt(0))));
}



procedure Call$$_module.__default.BuildFreeStack(_module._default.BuildFreeStack$A: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)))
         && $IsAlloc(a#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap), 
    k#0: int)
   returns (b#0: Seq Box
       where $Is(b#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)))
         && $IsAlloc(b#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap));
  // user-defined preconditions
  requires 0 < k#0;
  requires k#0 <= Seq#Length(a#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(b#0) == Seq#Length(a#0);
  free ensures (forall i#1: int :: 
    { $Unbox(Seq#Index(a#0, i#1)): DatatypeType } 
      { $Unbox(Seq#Index(b#0, i#1)): DatatypeType } 
    LitInt(0) <= i#1 && i#1 < k#0
       ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#1)): DatatypeType)
         && $IsA#_module.Node($Unbox(Seq#Index(a#0, i#1)): DatatypeType));
  ensures (forall i#1: int :: 
    { $Unbox(Seq#Index(a#0, i#1)): DatatypeType } 
      { $Unbox(Seq#Index(b#0, i#1)): DatatypeType } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < k#0
       ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#1)): DatatypeType, 
        $Unbox(Seq#Index(a#0, i#1)): DatatypeType));
  free ensures (forall i#3: int :: 
    { _module.__default.Sub(i#3, 1) } { $Unbox(Seq#Index(b#0, i#3)): DatatypeType } 
    k#0 <= i#3 && i#3 < Seq#Length(a#0)
       ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#3)): DatatypeType)
         && _module.__default.Sub#canCall(i#3, LitInt(1)));
  ensures (forall i#3: int :: 
    { _module.__default.Sub(i#3, 1) } { $Unbox(Seq#Index(b#0, i#3)): DatatypeType } 
    true
       ==> 
      k#0 <= i#3 && i#3 < Seq#Length(a#0)
       ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#3)): DatatypeType, 
        #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(i#3, LitInt(1)), LitInt(0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.BuildFreeStack(_module._default.BuildFreeStack$A: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)))
         && $IsAlloc(a#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap), 
    k#0: int)
   returns (b#0: Seq Box
       where $Is(b#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)))
         && $IsAlloc(b#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap), 
    $_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  // user-defined preconditions
  requires 0 < k#0;
  requires k#0 <= Seq#Length(a#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(b#0) == Seq#Length(a#0);
  free ensures (forall i#1: int :: 
    { $Unbox(Seq#Index(a#0, i#1)): DatatypeType } 
      { $Unbox(Seq#Index(b#0, i#1)): DatatypeType } 
    LitInt(0) <= i#1 && i#1 < k#0
       ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#1)): DatatypeType)
         && $IsA#_module.Node($Unbox(Seq#Index(a#0, i#1)): DatatypeType));
  ensures (forall i#1: int :: 
    { $Unbox(Seq#Index(a#0, i#1)): DatatypeType } 
      { $Unbox(Seq#Index(b#0, i#1)): DatatypeType } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < k#0
       ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#1)): DatatypeType, 
        $Unbox(Seq#Index(a#0, i#1)): DatatypeType));
  free ensures (forall i#3: int :: 
    { _module.__default.Sub(i#3, 1) } { $Unbox(Seq#Index(b#0, i#3)): DatatypeType } 
    k#0 <= i#3 && i#3 < Seq#Length(a#0)
       ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#3)): DatatypeType)
         && _module.__default.Sub#canCall(i#3, LitInt(1)));
  ensures (forall i#3: int :: 
    { _module.__default.Sub(i#3, 1) } { $Unbox(Seq#Index(b#0, i#3)): DatatypeType } 
    true
       ==> 
      k#0 <= i#3 && i#3 < Seq#Length(a#0)
       ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#3)): DatatypeType, 
        #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(i#3, LitInt(1)), LitInt(0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.BuildFreeStack(_module._default.BuildFreeStack$A: Ty, a#0: Seq Box, k#0: int)
   returns (b#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var i#4: int;
  var i#6: int;
  var ##a#1: int;
  var ##b#1: int;
  var ##s#0: Seq Box;
  var ##a#2: int;
  var ##b#2: int;
  var ##s#1: Seq Box;
  var $decr$loop#00: int;
  var ##a#0_0: int;
  var ##b#0_0: int;
  var ##s1#0_0: Seq Box;
  var ##i#0_0: int;
  var ##a#0_1: DatatypeType;
  var sum##0_0: int;
  var ##s#0_0: Seq Box;
  var sum##0_1: int;
  var ##s#0_1: Seq Box;
  var x##0_0: int;

    // AddMethodImpl: BuildFreeStack, Impl$$_module.__default.BuildFreeStack
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(193,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- DLL_Dafny.dfy(194,5)
    assume true;
    assume true;
    b#0 := a#0;
    assume {:captureState "DLL_Dafny.dfy(194,8)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(195,9)
    assume true;
    assume true;
    n#0 := k#0;
    assume {:captureState "DLL_Dafny.dfy(195,12)"} true;
    // ----- while statement ----- DLL_Dafny.dfy(197,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _module.__default.Dec(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
      n#0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> k#0 <= n#0;
      invariant $w$loop#0 ==> n#0 <= Seq#Length(b#0);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Seq#Length(b#0) == Seq#Length(a#0);
      free invariant $w$loop#0
         ==> (forall i#5: int :: 
          { $Unbox(Seq#Index(a#0, i#5)): DatatypeType } 
            { $Unbox(Seq#Index(b#0, i#5)): DatatypeType } 
          LitInt(0) <= i#5 && i#5 < k#0
             ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#5)): DatatypeType)
               && $IsA#_module.Node($Unbox(Seq#Index(a#0, i#5)): DatatypeType));
      invariant $w$loop#0
         ==> (forall i#5: int :: 
          { $Unbox(Seq#Index(a#0, i#5)): DatatypeType } 
            { $Unbox(Seq#Index(b#0, i#5)): DatatypeType } 
          true
             ==> 
            LitInt(0) <= i#5 && i#5 < k#0
             ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#5)): DatatypeType, 
              $Unbox(Seq#Index(a#0, i#5)): DatatypeType));
      free invariant $w$loop#0
         ==> (forall i#7: int :: 
          { _module.__default.Sub(i#7, 1) } { $Unbox(Seq#Index(b#0, i#7)): DatatypeType } 
          k#0 <= i#7 && i#7 < n#0
             ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#7)): DatatypeType)
               && _module.__default.Sub#canCall(i#7, LitInt(1)));
      invariant $w$loop#0
         ==> (forall i#7: int :: 
          { _module.__default.Sub(i#7, 1) } { $Unbox(Seq#Index(b#0, i#7)): DatatypeType } 
          true
             ==> 
            k#0 <= i#7 && i#7 < n#0
             ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#7)): DatatypeType, 
              #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(i#7, LitInt(1)), LitInt(0))));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant _module.__default.Dec(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
            n#0)
           <= $decr_init$loop#00
         && (_module.__default.Dec(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
              n#0)
             == $decr_init$loop#00
           ==> true);
    {
        assume {:captureState "DLL_Dafny.dfy(197,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (k#0 <= n#0)
            {
            }

            assume true;
            assume k#0 <= n#0 && n#0 <= Seq#Length(b#0);
            assume true;
            assume Seq#Length(b#0) == Seq#Length(a#0);
            havoc i#4;
            // Begin Comprehension WF check
            if (LitInt(0) <= i#4)
            {
            }

            if (LitInt(0) <= i#4 && i#4 < k#0)
            {
                assert {:subsumption 0} 0 <= i#4 && i#4 < Seq#Length(b#0);
                assert {:subsumption 0} 0 <= i#4 && i#4 < Seq#Length(a#0);
            }

            // End Comprehension WF check
            assume (forall i#5: int :: 
              { $Unbox(Seq#Index(a#0, i#5)): DatatypeType } 
                { $Unbox(Seq#Index(b#0, i#5)): DatatypeType } 
              LitInt(0) <= i#5 && i#5 < k#0
                 ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#5)): DatatypeType)
                   && $IsA#_module.Node($Unbox(Seq#Index(a#0, i#5)): DatatypeType));
            assume (forall i#5: int :: 
              { $Unbox(Seq#Index(a#0, i#5)): DatatypeType } 
                { $Unbox(Seq#Index(b#0, i#5)): DatatypeType } 
              true
                 ==> 
                LitInt(0) <= i#5 && i#5 < k#0
                 ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#5)): DatatypeType, 
                  $Unbox(Seq#Index(a#0, i#5)): DatatypeType));
            havoc i#6;
            // Begin Comprehension WF check
            if (k#0 <= i#6)
            {
            }

            if (k#0 <= i#6 && i#6 < n#0)
            {
                assert {:subsumption 0} 0 <= i#6 && i#6 < Seq#Length(b#0);
                ##a#1 := i#6;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#1, TInt, $Heap);
                ##b#1 := LitInt(1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#1, TInt, $Heap);
                assume _module.__default.Sub#canCall(i#6, LitInt(1));
            }

            // End Comprehension WF check
            assume (forall i#7: int :: 
              { _module.__default.Sub(i#7, 1) } { $Unbox(Seq#Index(b#0, i#7)): DatatypeType } 
              k#0 <= i#7 && i#7 < n#0
                 ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#7)): DatatypeType)
                   && _module.__default.Sub#canCall(i#7, LitInt(1)));
            assume (forall i#7: int :: 
              { _module.__default.Sub(i#7, 1) } { $Unbox(Seq#Index(b#0, i#7)): DatatypeType } 
              true
                 ==> 
                k#0 <= i#7 && i#7 < n#0
                 ==> _module.Node#Equal($Unbox(Seq#Index(b#0, i#7)): DatatypeType, 
                  #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(i#7, LitInt(1)), LitInt(0))));
            ##s#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap);
            assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
            ##a#2 := _module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#2, TInt, $Heap);
            ##b#2 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assume _module.__default.Dec#canCall(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
              n#0);
            assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0)
               && _module.__default.Dec#canCall(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
                n#0);
            assume false;
        }

        ##s#1 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#1, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap);
        assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        if (_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0)
           <= n#0)
        {
            break;
        }

        $decr$loop#00 := _module.__default.Dec(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
          n#0);
        // ----- assignment statement ----- DLL_Dafny.dfy(204,7)
        assume true;
        ##a#0_0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0_0, TInt, $Heap);
        ##b#0_0 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0_0, TInt, $Heap);
        assume _module.__default.Sub#canCall(n#0, LitInt(1));
        ##s1#0_0 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s1#0_0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap);
        ##i#0_0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#0_0, TInt, $Heap);
        ##a#0_1 := #_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(n#0, LitInt(1)), LitInt(0));
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0_1, Tclass._module.Node(_module._default.BuildFreeStack$A), $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#0_0;
        assert {:subsumption 0} ##i#0_0 < Seq#Length(##s1#0_0);
        assume LitInt(0) <= ##i#0_0 && ##i#0_0 < Seq#Length(##s1#0_0);
        assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), 
          b#0, 
          n#0, 
          $Box(#_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(n#0, LitInt(1)), LitInt(0))));
        assume _module.__default.Sub#canCall(n#0, LitInt(1))
           && _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), 
            b#0, 
            n#0, 
            $Box(#_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(n#0, LitInt(1)), LitInt(0))));
        b#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.BuildFreeStack$A), 
          b#0, 
          n#0, 
          $Box(#_module.Node.Node(Lit(#_module.Option.None()), _module.__default.Sub(n#0, LitInt(1)), LitInt(0))));
        assume {:captureState "DLL_Dafny.dfy(204,48)"} true;
        // ----- call statement ----- DLL_Dafny.dfy(205,19)
        // TrCallStmt: Before ProcessCallStmt
        ##s#0_0 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap);
        assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        // ProcessCallStmt: CheckSubrange
        sum##0_0 := _module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Props__dec__one(sum##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "DLL_Dafny.dfy(205,33)"} true;
        // ----- call statement ----- DLL_Dafny.dfy(206,26)
        // TrCallStmt: Before ProcessCallStmt
        ##s#0_1 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_1, TSeq(Tclass._module.Node(_module._default.BuildFreeStack$A)), $Heap);
        assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        // ProcessCallStmt: CheckSubrange
        sum##0_1 := _module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0_0 := n#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Props__dec__lower__bound(sum##0_1, x##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "DLL_Dafny.dfy(206,43)"} true;
        // ----- assignment statement ----- DLL_Dafny.dfy(207,7)
        assume true;
        assume true;
        n#0 := n#0 + 1;
        assume {:captureState "DLL_Dafny.dfy(207,14)"} true;
        // ----- loop termination check ----- DLL_Dafny.dfy(197,3)
        assert 0 <= $decr$loop#00
           || _module.__default.Dec(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
              n#0)
             == $decr$loop#00;
        assert _module.__default.Dec(_module.__default.seq_length(Tclass._module.Node(_module._default.BuildFreeStack$A), b#0), 
            n#0)
           < $decr$loop#00;
        assume true;
        assume true;
        assume (forall i#5: int :: 
          { $Unbox(Seq#Index(a#0, i#5)): DatatypeType } 
            { $Unbox(Seq#Index(b#0, i#5)): DatatypeType } 
          LitInt(0) <= i#5 && i#5 < k#0
             ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#5)): DatatypeType)
               && $IsA#_module.Node($Unbox(Seq#Index(a#0, i#5)): DatatypeType));
        assume (forall i#7: int :: 
          { _module.__default.Sub(i#7, 1) } { $Unbox(Seq#Index(b#0, i#7)): DatatypeType } 
          k#0 <= i#7 && i#7 < n#0
             ==> $IsA#_module.Node($Unbox(Seq#Index(b#0, i#7)): DatatypeType)
               && _module.__default.Sub#canCall(i#7, LitInt(1)));
    }
}



procedure CheckWellformed$$_module.__default.Alloc(_module._default.Alloc$A: Ty, initial_len#0: int)
   returns (l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Alloc$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Alloc$A), $Heap));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Alloc(_module._default.Alloc$A: Ty, initial_len#0: int)
   returns (l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Alloc$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Alloc$A), $Heap));
  // user-defined preconditions
  requires initial_len#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0);
  free ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     && 
    _module.__default.Inv(_module._default.Alloc$A, l#0)
     && $Is(_module.DList.nodes(l#0), TSeq(Tclass._module.Node(_module._default.Alloc$A)))
     && $Is(_module.DList.s(l#0), TSeq(_module._default.Alloc$A))
     && $Is(_module.DList.f(l#0), TSeq(TInt))
     && $Is(_module.DList.g(l#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.Alloc$A, 
      _module.DList.nodes(l#0), 
      _module.DList.freeStack(l#0), 
      _module.DList.s(l#0), 
      _module.DList.f(l#0), 
      _module.DList.g(l#0));
  free ensures _module.__default.Seq#canCall(_module._default.Alloc$A, l#0);
  ensures Seq#Equal(_module.__default.Seq(_module._default.Alloc$A, l#0), Seq#Empty(): Seq Box);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Alloc(_module._default.Alloc$A: Ty, initial_len#0: int)
   returns (l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Alloc$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Alloc$A), $Heap), 
    $_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  // user-defined preconditions
  requires initial_len#0 > 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0);
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.f(l#0)) == Seq#Length(_module.DList.s(l#0)));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.g(l#0)) == Seq#Length(_module.DList.nodes(l#0)));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.nodes(l#0)) > 0);
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || $Unbox(Seq#Index(_module.DList.g(l#0), LitInt(0))): int
             == _module.__default.sentinel());
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || LitInt(0) <= _module.DList.freeStack(l#0));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || _module.DList.freeStack(l#0) < Seq#Length(_module.DList.nodes(l#0)));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#2: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l#0), i#2)): int } 
            true
               ==> (LitInt(0) <= i#2 && i#2 < Seq#Length(_module.DList.f(l#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l#0), i#2)): int)
                 && (LitInt(0) <= i#2 && i#2 < Seq#Length(_module.DList.f(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l#0), i#2)): int
                     < Seq#Length(_module.DList.nodes(l#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#3: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#3)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#3 && i#3 < Seq#Length(_module.DList.f(l#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#3)): int)): int
                 == i#3));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int } 
            true
               ==> (LitInt(0) <= p#7 && p#7 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int)
                 && (LitInt(0) <= p#7 && p#7 < Seq#Length(_module.DList.g(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int
                     < Seq#Length(_module.DList.s(l#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#8: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#8)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#8 && p#8 < Seq#Length(_module.DList.g(l#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#8)): DatatypeType))
                 && (LitInt(0) <= p#8 && p#8 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#8)): DatatypeType)
                     < Seq#Length(_module.DList.g(l#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#9: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#9)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#9)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#9 && p#9 < Seq#Length(_module.DList.g(l#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l#0), p#9)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#9)): DatatypeType)))));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#10: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#10)): int } 
            true
               ==> 
              LitInt(0) <= p#10
                 && p#10 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#10)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l#0), p#10)): int
                 == _module.__default.sentinel()
               ==> p#10 == LitInt(0)));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#11: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#11)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#11)): int)): int } 
              { Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#11)): int) } 
            true
               ==> 
              LitInt(0) <= p#11
                 && p#11 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#11)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l#0), p#11)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#11)): int)): int
                   == p#11
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#11)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#11)): int)))));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#12: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#12)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#12)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#12
                 && p#12 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#12)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#12)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#12)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l#0))
                   then $Unbox(Seq#Index(_module.DList.f(l#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#12)): int, LitInt(1)))): int
                   else 0)));
  ensures _module.__default.Inv#canCall(_module._default.Alloc$A, l#0)
     ==> _module.__default.Inv(_module._default.Alloc$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Alloc$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Alloc$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#13: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#13)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#13)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#13
                     && p#13 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#13)): int
                   ==> true)
                 && (LitInt(0) <= p#13
                     && p#13 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#13)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#13)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l#0), p#13)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l#0), p#13)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l#0), p#13)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l#0)), LitInt(1)))): int)))));
  free ensures _module.__default.Seq#canCall(_module._default.Alloc$A, l#0);
  ensures Seq#Equal(_module.__default.Seq(_module._default.Alloc$A, l#0), Seq#Empty(): Seq Box);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Alloc(_module._default.Alloc$A: Ty, initial_len#0: int)
   returns (l#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var nodes#0: Seq Box
     where $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Alloc$A)))
       && $IsAlloc(nodes#0, TSeq(Tclass._module.Node(_module._default.Alloc$A)), $Heap);
  var ##length#0: int;
  var ##a#0: DatatypeType;
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(Tclass._module.Node(_module._default.Alloc$A)))
       && $IsAlloc($rhs##0, TSeq(Tclass._module.Node(_module._default.Alloc$A)), $Heap);
  var a##0: Seq Box;
  var k##0: int;
  var p#14: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: int;

    // AddMethodImpl: Alloc, Impl$$_module.__default.Alloc
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(216,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- DLL_Dafny.dfy(217,13)
    assume true;
    ##length#0 := initial_len#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##length#0, TInt, $Heap);
    ##a#0 := Lit(#_module.Node.Node(Lit(#_module.Option.None()), LitInt(0), LitInt(0)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, Tclass._module.Node(_module._default.Alloc$A), $Heap);
    assume _module.__default.seq_alloc#canCall(Tclass._module.Node(_module._default.Alloc$A), 
      initial_len#0, 
      $Box(Lit(#_module.Node.Node(Lit(#_module.Option.None()), LitInt(0), LitInt(0)))));
    assume _module.__default.seq_alloc#canCall(Tclass._module.Node(_module._default.Alloc$A), 
      initial_len#0, 
      $Box(Lit(#_module.Node.Node(Lit(#_module.Option.None()), LitInt(0), LitInt(0)))));
    nodes#0 := _module.__default.seq_alloc(Tclass._module.Node(_module._default.Alloc$A), 
      initial_len#0, 
      $Box(Lit(#_module.Node.Node(Lit(#_module.Option.None()), LitInt(0), LitInt(0)))));
    assume {:captureState "DLL_Dafny.dfy(217,61)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(218,26)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type seq<Node<A>>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := nodes#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    k##0 := LitInt(1);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.BuildFreeStack(_module._default.Alloc$A, a##0, k##0);
    // TrCallStmt: After ProcessCallStmt
    nodes#0 := $rhs##0;
    assume {:captureState "DLL_Dafny.dfy(218,35)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(219,5)
    assume true;
    assert 0 <= initial_len#0;
    havoc p#14;
    // Begin Comprehension WF check
    if (*)
    {
        $oldHeap#0 := $Heap;
        havoc $Heap;
        assume $IsGoodHeap($Heap);
        assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
        $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (p#14 == LitInt(0))
        {
            assume lambdaResult#0 == _module.__default.sentinel();
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#0, TInt);
        }
        else
        {
            assume lambdaResult#0 == _module.__default.unused();
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#0, TInt);
        }

        assume false;
    }

    // End Comprehension WF check
    assert {:subsumption 0} (forall seqinit#0#i0#0: int :: 
      0 <= seqinit#0#i0#0 && seqinit#0#i0#0 < initial_len#0
         ==> Requires1(TInt, 
          TInt, 
          $Heap, 
          Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                Handle1((lambda $l#0#heap#0: Heap, $l#0#p#0: Box :: 
                    $Box((if $Unbox($l#0#p#0): int == LitInt(0)
                         then _module.__default.sentinel()
                         else _module.__default.unused()))), 
                  (lambda $l#0#heap#0: Heap, $l#0#p#0: Box :: $IsBox($l#0#p#0, TInt)), 
                  (lambda $l#0#heap#0: Heap, $l#0#p#0: Box :: 
                    SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(seqinit#0#i0#0)));
    assume true;
    l#0 := #_module.DList.DList(nodes#0, 
      initial_len#0 - 1, 
      Lit(Seq#Empty(): Seq Box), 
      Lit(Seq#Empty(): Seq Box), 
      Seq#Create(TInt, 
        $Heap, 
        initial_len#0, 
        Lit(AtLayer((lambda $l#3#ly#0: LayerType :: 
              Handle1((lambda $l#3#heap#0: Heap, $l#3#p#0: Box :: 
                  $Box((if $Unbox($l#3#p#0): int == LitInt(0)
                       then _module.__default.sentinel()
                       else _module.__default.unused()))), 
                (lambda $l#3#heap#0: Heap, $l#3#p#0: Box :: $IsBox($l#3#p#0, TInt)), 
                (lambda $l#3#heap#0: Heap, $l#3#p#0: Box :: 
                  SetRef_to_SetBox((lambda $l#3#o#0: ref :: false))))), 
            $LS($LZ)))));
    assume {:captureState "DLL_Dafny.dfy(219,104)"} true;
}



procedure CheckWellformed$$_module.__default.Free(_module._default.Free$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Free$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Free$A), $Heap)
         && $IsA#_module.DList(l#0));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Free(_module._default.Free$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Free$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Free$A), $Heap)
         && $IsA#_module.DList(l#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Free(_module._default.Free$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Free$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Free$A), $Heap)
         && $IsA#_module.DList(l#0))
   returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.Expand(_module._default.Expand$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Expand$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Expand$A), $Heap)
         && $IsA#_module.DList(l#0))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Expand$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Expand$A), $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Expand(_module._default.Expand$A: Ty, l#0: DatatypeType) returns (l'#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var x#0: int;
  var ##l#2: DatatypeType;
  var ##p#0: int;
  var ##l#3: DatatypeType;
  var ##p#1: int;

    // AddMethodImpl: Expand, CheckWellformed$$_module.__default.Expand
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(229,7): initial state"} true;
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.Expand$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.Expand$A, l#0);
    assume _module.__default.Inv(_module._default.Expand$A, l#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc l'#0;
    assume {:captureState "DLL_Dafny.dfy(231,13): post-state"} true;
    ##l#1 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.Expand$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.Expand$A, l'#0);
    assume _module.__default.Inv(_module._default.Expand$A, l'#0);
    assume _module.DList.DList_q(l'#0);
    assume _module.DList.DList_q(l#0);
    assume Seq#Equal(_module.DList.s(l'#0), _module.DList.s(l#0));
    havoc x#0;
    if (*)
    {
        ##l#2 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.Expand$A), $Heap);
        ##p#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#0, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.Expand$A, l#0, x#0);
        assume _module.__default.ValidPtr(_module._default.Expand$A, l#0, x#0);
        ##l#3 := l'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.Expand$A), $Heap);
        ##p#1 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#1, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.Expand$A, l'#0, x#0);
        assume _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#0);
        assume _module.DList.DList_q(l'#0);
        assert 0 <= x#0 && x#0 < Seq#Length(_module.DList.g(l'#0));
        assume _module.DList.DList_q(l#0);
        assert 0 <= x#0 && x#0 < Seq#Length(_module.DList.g(l#0));
        assume $Unbox(Seq#Index(_module.DList.g(l'#0), x#0)): int
           == $Unbox(Seq#Index(_module.DList.g(l#0), x#0)): int;
    }
    else
    {
        assume _module.__default.ValidPtr(_module._default.Expand$A, l#0, x#0)
           ==> _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#0)
             && $Unbox(Seq#Index(_module.DList.g(l'#0), x#0)): int
               == $Unbox(Seq#Index(_module.DList.g(l#0), x#0)): int;
    }

    assume (forall x#1: int :: 
      { $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int } 
        { $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int } 
        { _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1) } 
        { _module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1) } 
      true
         ==> (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
             ==> _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1))
           && (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
             ==> $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int
               == $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int));
    assume _module.DList.DList_q(l'#0);
    assume _module.DList.freeStack(l'#0) != 0;
    assume _module.DList.DList_q(l'#0);
    assume _module.DList.DList_q(l'#0);
    assert 0 <= _module.DList.freeStack(l'#0)
       && _module.DList.freeStack(l'#0) < Seq#Length(_module.DList.nodes(l'#0));
    assume _module.Node.Node_q($Unbox(Seq#Index(_module.DList.nodes(l'#0), _module.DList.freeStack(l'#0))): DatatypeType);
    assume _module.Option.None_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), _module.DList.freeStack(l'#0))): DatatypeType));
}



procedure Call$$_module.__default.Expand(_module._default.Expand$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Expand$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Expand$A), $Heap)
         && $IsA#_module.DList(l#0))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Expand$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Expand$A), $Heap));
  // user-defined preconditions
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.f(l#0)) == Seq#Length(_module.DList.s(l#0)));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.g(l#0)) == Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.nodes(l#0)) > 0);
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || $Unbox(Seq#Index(_module.DList.g(l#0), LitInt(0))): int
             == _module.__default.sentinel());
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || LitInt(0) <= _module.DList.freeStack(l#0));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || _module.DList.freeStack(l#0) < Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#0: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int } 
            true
               ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int)
                 && (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int
                     < Seq#Length(_module.DList.nodes(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#1: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#1 && i#1 < Seq#Length(_module.DList.f(l#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int
                 == i#1));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#0: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int } 
            true
               ==> (LitInt(0) <= p#0 && p#0 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int)
                 && (LitInt(0) <= p#0 && p#0 < Seq#Length(_module.DList.g(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int
                     < Seq#Length(_module.DList.s(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#1: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#1)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#1)): DatatypeType))
                 && (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#1)): DatatypeType)
                     < Seq#Length(_module.DList.g(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#2: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#2)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#2 && p#2 < Seq#Length(_module.DList.g(l#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l#0), p#2)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType)))));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#3: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int } 
            true
               ==> 
              LitInt(0) <= p#3
                 && p#3 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int
                 == _module.__default.sentinel()
               ==> p#3 == LitInt(0)));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#4: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int)): int } 
              { Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int) } 
            true
               ==> 
              LitInt(0) <= p#4
                 && p#4 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int)): int
                   == p#4
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#4)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int)))));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#5: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#5)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#5
                 && p#5 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#5)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l#0))
                   then $Unbox(Seq#Index(_module.DList.f(l#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int, LitInt(1)))): int
                   else 0)));
  requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#6: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#6
                     && p#6 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int
                   ==> true)
                 && (LitInt(0) <= p#6
                     && p#6 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l#0)), LitInt(1)))): int)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0);
  free ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     && 
    _module.__default.Inv(_module._default.Expand$A, l'#0)
     && $Is(_module.DList.nodes(l'#0), TSeq(Tclass._module.Node(_module._default.Expand$A)))
     && $Is(_module.DList.s(l'#0), TSeq(_module._default.Expand$A))
     && $Is(_module.DList.f(l'#0), TSeq(TInt))
     && $Is(_module.DList.g(l'#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.Expand$A, 
      _module.DList.nodes(l'#0), 
      _module.DList.freeStack(l'#0), 
      _module.DList.s(l'#0), 
      _module.DList.f(l'#0), 
      _module.DList.g(l'#0));
  free ensures _module.DList.DList_q(l'#0) && _module.DList.DList_q(l#0);
  ensures Seq#Equal(_module.DList.s(l'#0), _module.DList.s(l#0));
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int } 
      { $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1) } 
    _module.__default.ValidPtr#canCall(_module._default.Expand$A, l#0, x#1)
       && (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
         ==> _module.__default.ValidPtr#canCall(_module._default.Expand$A, l'#0, x#1))
       && (
        (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1))
         ==> _module.__default.ValidPtr#canCall(_module._default.Expand$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
             ==> _module.DList.DList_q(l'#0) && _module.DList.DList_q(l#0))));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int } 
      { $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1) } 
    true
       ==> (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1))
         && (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
           ==> $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int
             == $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int));
  free ensures _module.DList.DList_q(l'#0)
     && (_module.DList.freeStack(l'#0) != 0
       ==> _module.DList.DList_q(l'#0)
         && _module.DList.DList_q(l'#0)
         && _module.Node.Node_q($Unbox(Seq#Index(_module.DList.nodes(l'#0), _module.DList.freeStack(l'#0))): DatatypeType));
  ensures _module.DList.freeStack(l'#0) != 0;
  ensures _module.Option.None_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), _module.DList.freeStack(l'#0))): DatatypeType));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Expand(_module._default.Expand$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Expand$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Expand$A), $Heap)
         && $IsA#_module.DList(l#0))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Expand$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Expand$A), $Heap), 
    $_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Inv#canCall(_module._default.Expand$A, l#0)
     && 
    _module.__default.Inv(_module._default.Expand$A, l#0)
     && $Is(_module.DList.nodes(l#0), TSeq(Tclass._module.Node(_module._default.Expand$A)))
     && $Is(_module.DList.s(l#0), TSeq(_module._default.Expand$A))
     && $Is(_module.DList.f(l#0), TSeq(TInt))
     && $Is(_module.DList.g(l#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.Expand$A, 
      _module.DList.nodes(l#0), 
      _module.DList.freeStack(l#0), 
      _module.DList.s(l#0), 
      _module.DList.f(l#0), 
      _module.DList.g(l#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0);
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.f(l'#0)) == Seq#Length(_module.DList.s(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.g(l'#0)) == Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.nodes(l'#0)) > 0);
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || $Unbox(Seq#Index(_module.DList.g(l'#0), LitInt(0))): int
             == _module.__default.sentinel());
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || LitInt(0) <= _module.DList.freeStack(l'#0));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || _module.DList.freeStack(l'#0) < Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#6: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int
                     < Seq#Length(_module.DList.nodes(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(_module.DList.f(l'#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int
                 == i#7));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#21: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#21)): int } 
            true
               ==> (LitInt(0) <= p#21 && p#21 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.__default.unused()
                     <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#21)): int)
                 && (LitInt(0) <= p#21 && p#21 < Seq#Length(_module.DList.g(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l'#0), p#21)): int
                     < Seq#Length(_module.DList.s(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#22: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#22)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#22)): DatatypeType))
                 && (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#22)): DatatypeType)
                     < Seq#Length(_module.DList.g(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#23: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#23)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#23 && p#23 < Seq#Length(_module.DList.g(l'#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l'#0), p#23)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType)))));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#24: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int } 
            true
               ==> 
              LitInt(0) <= p#24
                 && p#24 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int
                 == _module.__default.sentinel()
               ==> p#24 == LitInt(0)));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#25: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int)): int } 
              { Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int) } 
            true
               ==> 
              LitInt(0) <= p#25
                 && p#25 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int)): int
                   == p#25
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#25)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int)))));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#26: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#26)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#26
                 && p#26 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#26)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l'#0))
                   then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int, LitInt(1)))): int
                   else 0)));
  ensures _module.__default.Inv#canCall(_module._default.Expand$A, l'#0)
     ==> _module.__default.Inv(_module._default.Expand$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Expand$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Expand$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#27: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#27
                     && p#27 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int
                   ==> true)
                 && (LitInt(0) <= p#27
                     && p#27 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l'#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l'#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l'#0)), LitInt(1)))): int)))));
  free ensures _module.DList.DList_q(l'#0) && _module.DList.DList_q(l#0);
  ensures Seq#Equal(_module.DList.s(l'#0), _module.DList.s(l#0));
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int } 
      { $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1) } 
    _module.__default.ValidPtr#canCall(_module._default.Expand$A, l#0, x#1)
       && (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
         ==> _module.__default.ValidPtr#canCall(_module._default.Expand$A, l'#0, x#1))
       && (
        (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1))
         ==> _module.__default.ValidPtr#canCall(_module._default.Expand$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
             ==> _module.DList.DList_q(l'#0) && _module.DList.DList_q(l#0))));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int } 
      { $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1) } 
    true
       ==> (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.Expand$A, l'#0, x#1))
         && (_module.__default.ValidPtr(_module._default.Expand$A, l#0, x#1)
           ==> $Unbox(Seq#Index(_module.DList.g(l'#0), x#1)): int
             == $Unbox(Seq#Index(_module.DList.g(l#0), x#1)): int));
  free ensures _module.DList.DList_q(l'#0)
     && (_module.DList.freeStack(l'#0) != 0
       ==> _module.DList.DList_q(l'#0)
         && _module.DList.DList_q(l'#0)
         && _module.Node.Node_q($Unbox(Seq#Index(_module.DList.nodes(l'#0), _module.DList.freeStack(l'#0))): DatatypeType));
  ensures _module.DList.freeStack(l'#0) != 0;
  ensures _module.Option.None_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), _module.DList.freeStack(l'#0))): DatatypeType));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Expand(_module._default.Expand$A: Ty, l#0: DatatypeType)
   returns (l'#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var nodes#0: Seq Box;
  var freeStack#0: int;
  var s#0: Seq Box;
  var f#0: Seq Box;
  var g#0: Seq Box;
  var let#0#0#0: DatatypeType;
  var len#0: int;
  var ##s#0: Seq Box;
  var len'#0: int;
  var ##a#0: int;
  var ##b#0: int;
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(Tclass._module.Node(_module._default.Expand$A)))
       && $IsAlloc($rhs##0, TSeq(Tclass._module.Node(_module._default.Expand$A)), $Heap);
  var s##0: Seq Box;
  var newlen##0: int;
  var a##0: Box;
  var ##a#1: int;
  var ##b#1: int;
  var ##a#2: int;
  var ##b#2: int;
  var $rhs##1: Seq Box
     where $Is($rhs##1, TSeq(Tclass._module.Node(_module._default.Expand$A)))
       && $IsAlloc($rhs##1, TSeq(Tclass._module.Node(_module._default.Expand$A)), $Heap);
  var a##1: Seq Box;
  var k##0: int;
  var ##a#3: int;
  var ##b#3: int;
  var ##a#4: int;
  var ##b#4: int;
  var i#8: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: int;

    // AddMethodImpl: Expand, Impl$$_module.__default.Expand
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(235,0): initial state"} true;
    $_reverifyPost := false;
    havoc nodes#0;
    assume $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Expand$A)))
       && $IsAlloc(nodes#0, TSeq(Tclass._module.Node(_module._default.Expand$A)), $Heap);
    havoc freeStack#0;
    havoc s#0;
    assume $Is(s#0, TSeq(_module._default.Expand$A))
       && $IsAlloc(s#0, TSeq(_module._default.Expand$A), $Heap);
    havoc f#0;
    assume $Is(f#0, TSeq(TInt)) && $IsAlloc(f#0, TSeq(TInt), $Heap);
    havoc g#0;
    assume $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap);
    assume let#0#0#0 == l#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.DList(_module._default.Expand$A));
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume #_module.DList.DList(nodes#0, freeStack#0, s#0, f#0, g#0) == let#0#0#0;
    // ----- assignment statement ----- DLL_Dafny.dfy(238,11)
    assume true;
    ##s#0 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(Tclass._module.Node(_module._default.Expand$A)), $Heap);
    assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.Expand$A), nodes#0);
    assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.Expand$A), nodes#0);
    len#0 := _module.__default.seq_length(Tclass._module.Node(_module._default.Expand$A), nodes#0);
    assume {:captureState "DLL_Dafny.dfy(238,30)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(241,12)
    assume true;
    ##a#0 := len#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := len#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assume _module.__default.Add#canCall(len#0, len#0);
    assume _module.__default.Add#canCall(len#0, len#0);
    len'#0 := _module.__default.Add(len#0, len#0);
    assume {:captureState "DLL_Dafny.dfy(241,27)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(242,21)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type seq<Node<A>>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := nodes#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    newlen##0 := len'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := $Box(#_module.Node.Node(Lit(#_module.Option.None()), freeStack#0, LitInt(0)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.SeqResize(Tclass._module.Node(_module._default.Expand$A), s##0, newlen##0, a##0);
    // TrCallStmt: After ProcessCallStmt
    nodes#0 := $rhs##0;
    assume {:captureState "DLL_Dafny.dfy(242,59)"} true;
    // ----- assume statement ----- DLL_Dafny.dfy(243,3)
    ##a#1 := len#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    ##b#1 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TInt, $Heap);
    assume _module.__default.Add#canCall(len#0, LitInt(1));
    ##a#2 := len#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, TInt, $Heap);
    ##b#2 := len#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, TInt, $Heap);
    assume _module.__default.Add#canCall(len#0, len#0);
    assume _module.__default.Add#canCall(len#0, LitInt(1))
       && _module.__default.Add#canCall(len#0, len#0);
    assume _module.__default.Add(len#0, LitInt(1)) <= _module.__default.Add(len#0, len#0);
    // ----- call statement ----- DLL_Dafny.dfy(244,26)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type seq<Node<A>>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := nodes#0;
    ##a#3 := len#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, TInt, $Heap);
    ##b#3 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, TInt, $Heap);
    assume _module.__default.Add#canCall(len#0, LitInt(1));
    assume _module.__default.Add#canCall(len#0, LitInt(1));
    // ProcessCallStmt: CheckSubrange
    k##0 := _module.__default.Add(len#0, LitInt(1));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.__default.BuildFreeStack(_module._default.Expand$A, a##1, k##0);
    // TrCallStmt: After ProcessCallStmt
    nodes#0 := $rhs##1;
    assume {:captureState "DLL_Dafny.dfy(244,45)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(245,6)
    assume true;
    ##a#4 := len'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#4, TInt, $Heap);
    ##b#4 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#4, TInt, $Heap);
    assume _module.__default.Sub#canCall(len'#0, LitInt(1));
    assert 0 <= Seq#Length(nodes#0);
    havoc i#8;
    // Begin Comprehension WF check
    if (*)
    {
        $oldHeap#0 := $Heap;
        havoc $Heap;
        assume $IsGoodHeap($Heap);
        assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
        $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (LitInt(0) <= i#8)
        {
        }

        if (LitInt(0) <= i#8 && i#8 < Seq#Length(nodes#0))
        {
            if (i#8 < Seq#Length(g#0))
            {
                assert 0 <= i#8 && i#8 < Seq#Length(g#0);
                assume lambdaResult#0 == $Unbox(Seq#Index(g#0, i#8)): int;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, TInt);
            }
            else
            {
                assume lambdaResult#0 == _module.__default.unused();
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, TInt);
            }
        }

        assume false;
    }

    // End Comprehension WF check
    assert {:subsumption 0} (forall seqinit#0#i0#0: int :: 
      0 <= seqinit#0#i0#0 && seqinit#0#i0#0 < Seq#Length(nodes#0)
         ==> Requires1(TInt, 
          TInt, 
          $Heap, 
          Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                Handle1((lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                    $Box((if $Unbox($l#0#i#0): int < Seq#Length(g#0)
                         then $Unbox(Seq#Index(g#0, $Unbox($l#0#i#0): int)): int
                         else _module.__default.unused()))), 
                  (lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                    $IsBox($l#0#i#0, TInt)
                       && 
                      LitInt(0) <= $Unbox($l#0#i#0): int
                       && $Unbox($l#0#i#0): int < Seq#Length(nodes#0)), 
                  (lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                    SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(seqinit#0#i0#0)));
    assume _module.__default.Sub#canCall(len'#0, LitInt(1));
    l'#0 := #_module.DList.DList(nodes#0, 
      _module.__default.Sub(len'#0, LitInt(1)), 
      s#0, 
      f#0, 
      Seq#Create(TInt, 
        $Heap, 
        Seq#Length(nodes#0), 
        Lit(AtLayer((lambda $l#3#ly#0: LayerType :: 
              Handle1((lambda $l#3#heap#0: Heap, $l#3#i#0: Box :: 
                  $Box((if $Unbox($l#3#i#0): int < Seq#Length(g#0)
                       then $Unbox(Seq#Index(g#0, $Unbox($l#3#i#0): int)): int
                       else _module.__default.unused()))), 
                (lambda $l#3#heap#0: Heap, $l#3#i#0: Box :: 
                  $IsBox($l#3#i#0, TInt)
                     && 
                    LitInt(0) <= $Unbox($l#3#i#0): int
                     && $Unbox($l#3#i#0): int < Seq#Length(nodes#0)), 
                (lambda $l#3#heap#0: Heap, $l#3#i#0: Box :: 
                  SetRef_to_SetBox((lambda $l#3#o#0: ref :: false))))), 
            $LS($LZ)))));
    assume {:captureState "DLL_Dafny.dfy(246,69)"} true;
}



procedure CheckWellformed$$_module.__default.Remove__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    index#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Remove__SeqInit(g#0: Seq Box, index#0: int) returns (g'#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: Remove_SeqInit, CheckWellformed$$_module.__default.Remove__SeqInit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(249,13): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc g'#0;
    assume {:captureState "DLL_Dafny.dfy(250,15): post-state"} true;
    assume Seq#Length(g'#0) == Seq#Length(g#0);
    havoc x#0;
    if (*)
    {
        assume LitInt(0) <= x#0;
        assume x#0 < Seq#Length(g#0);
        if (*)
        {
            assert 0 <= x#0 && x#0 < Seq#Length(g#0);
            assume $Unbox(Seq#Index(g#0, x#0)): int == index#0;
            assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
            assume $Unbox(Seq#Index(g'#0, x#0)): int == _module.__default.unused();
        }
        else
        {
            assume $Unbox(Seq#Index(g#0, x#0)): int != index#0;
            if (*)
            {
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                assume index#0 < $Unbox(Seq#Index(g#0, x#0)): int;
                assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                ##a#0 := $Unbox(Seq#Index(g#0, x#0)): int;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, TInt, $Heap);
                ##b#0 := LitInt(1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, TInt, $Heap);
                assume _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1));
                assume $Unbox(Seq#Index(g'#0, x#0)): int
                   == _module.__default.Sub($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1));
            }
            else
            {
                assume $Unbox(Seq#Index(g#0, x#0)): int <= index#0;
                assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                assume $Unbox(Seq#Index(g'#0, x#0)): int == $Unbox(Seq#Index(g#0, x#0)): int;
            }
        }
    }
    else
    {
        assume LitInt(0) <= x#0 && x#0 < Seq#Length(g#0)
           ==> (if $Unbox(Seq#Index(g#0, x#0)): int == index#0
             then $Unbox(Seq#Index(g'#0, x#0)): int == _module.__default.unused()
             else (if index#0 < $Unbox(Seq#Index(g#0, x#0)): int
               then $Unbox(Seq#Index(g'#0, x#0)): int
                 == _module.__default.Sub($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1))
               else $Unbox(Seq#Index(g'#0, x#0)): int == $Unbox(Seq#Index(g#0, x#0)): int));
    }

    assume (forall x#1: int :: 
      { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
      true
         ==> 
        LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
         ==> (if $Unbox(Seq#Index(g#0, x#1)): int == index#0
           then $Unbox(Seq#Index(g'#0, x#1)): int == _module.__default.unused()
           else (if index#0 < $Unbox(Seq#Index(g#0, x#1)): int
             then $Unbox(Seq#Index(g'#0, x#1)): int
               == _module.__default.Sub($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
             else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
}



procedure Call$$_module.__default.Remove__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    index#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(g'#0) == Seq#Length(g#0);
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> 
      $Unbox(Seq#Index(g#0, x#1)): int != index#0
       ==> 
      index#0 < $Unbox(Seq#Index(g#0, x#1)): int
       ==> _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1)));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    true
       ==> 
      LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> (if $Unbox(Seq#Index(g#0, x#1)): int == index#0
         then $Unbox(Seq#Index(g'#0, x#1)): int == _module.__default.unused()
         else (if index#0 < $Unbox(Seq#Index(g#0, x#1)): int
           then $Unbox(Seq#Index(g'#0, x#1)): int
             == _module.__default.Sub($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
           else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Remove__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    index#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(g'#0) == Seq#Length(g#0);
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> 
      $Unbox(Seq#Index(g#0, x#1)): int != index#0
       ==> 
      index#0 < $Unbox(Seq#Index(g#0, x#1)): int
       ==> _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1)));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    true
       ==> 
      LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> (if $Unbox(Seq#Index(g#0, x#1)): int == index#0
         then $Unbox(Seq#Index(g'#0, x#1)): int == _module.__default.unused()
         else (if index#0 < $Unbox(Seq#Index(g#0, x#1)): int
           then $Unbox(Seq#Index(g'#0, x#1)): int
             == _module.__default.Sub($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
           else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Remove__SeqInit(g#0: Seq Box, index#0: int) returns (g'#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: int;
  var ##a#1: int;
  var ##b#1: int;
  var ##len#0: int;
  var ##func#0: HandleType;

    // AddMethodImpl: Remove_SeqInit, Impl$$_module.__default.Remove__SeqInit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(256,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- DLL_Dafny.dfy(257,8)
    assume true;
    havoc x#2;
    // Begin Comprehension WF check
    if (*)
    {
        $oldHeap#0 := $Heap;
        havoc $Heap;
        assume $IsGoodHeap($Heap);
        assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
        $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (LitInt(0) <= x#2)
        {
        }

        if (LitInt(0) <= x#2 && x#2 < Seq#Length(g#0))
        {
            assert 0 <= x#2 && x#2 < Seq#Length(g#0);
            if ($Unbox(Seq#Index(g#0, x#2)): int == index#0)
            {
                assume lambdaResult#0 == _module.__default.unused();
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, TInt);
            }
            else
            {
                assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                if ($Unbox(Seq#Index(g#0, x#2)): int > index#0)
                {
                    assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                    ##a#1 := $Unbox(Seq#Index(g#0, x#2)): int;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##a#1, TInt, $Heap);
                    ##b#1 := LitInt(1);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##b#1, TInt, $Heap);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame#l0[$o, $f]);
                    assume _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    assume lambdaResult#0
                       == _module.__default.Sub($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    assume _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    // CheckWellformedWithResult: any expression
                    assume $Is(lambdaResult#0, TInt);
                }
                else
                {
                    assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                    assume lambdaResult#0 == $Unbox(Seq#Index(g#0, x#2)): int;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(lambdaResult#0, TInt);
                }
            }
        }

        assume false;
    }

    // End Comprehension WF check
    ##len#0 := Seq#Length(g#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##len#0, TInt, $Heap);
    ##func#0 := Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
          Handle1((lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              $Box((if $Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int == index#0
                   then _module.__default.unused()
                   else (if $Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int > index#0
                     then _module.__default.Sub($Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int, LitInt(1))
                     else $Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int)))), 
            (lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              $IsBox($l#1#x#0, TInt)
                 && 
                LitInt(0) <= $Unbox($l#1#x#0): int
                 && $Unbox($l#1#x#0): int < Seq#Length(g#0)), 
            (lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
        $LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##func#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap);
    assert {:subsumption 0} ##len#0 >= LitInt(0);
    assume ##len#0 >= LitInt(0);
    assert {:subsumption 0} (forall i#0: int :: 
      { Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)) } 
      true
         ==> 
        LitInt(0) <= i#0 && i#0 < ##len#0
         ==> Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)));
    assume (forall i#0: int :: 
      { Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)) } 
      true
         ==> 
        LitInt(0) <= i#0 && i#0 < ##len#0
         ==> Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)));
    assume _module.__default.SeqInit#canCall(TInt, 
      Seq#Length(g#0), 
      Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
            Handle1((lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                $Box((if $Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int == index#0
                     then _module.__default.unused()
                     else (if $Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int > index#0
                       then _module.__default.Sub($Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int, LitInt(1))
                       else $Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int)))), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                $IsBox($l#2#x#0, TInt)
                   && 
                  LitInt(0) <= $Unbox($l#2#x#0): int
                   && $Unbox($l#2#x#0): int < Seq#Length(g#0)), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
          $LS($LZ))));
    assume (forall $l#3#x#0: int :: 
        LitInt(0) <= $l#3#x#0 && $l#3#x#0 < Seq#Length(g#0)
           ==> 
          $Unbox(Seq#Index(g#0, $l#3#x#0)): int != index#0
           ==> 
          $Unbox(Seq#Index(g#0, $l#3#x#0)): int > index#0
           ==> _module.__default.Sub#canCall($Unbox(Seq#Index(g#0, $l#3#x#0)): int, LitInt(1)))
       && _module.__default.SeqInit#canCall(TInt, 
        Seq#Length(g#0), 
        Lit(AtLayer((lambda $l#4#ly#0: LayerType :: 
              Handle1((lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  $Box((if $Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int == index#0
                       then _module.__default.unused()
                       else (if $Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int > index#0
                         then _module.__default.Sub($Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int, LitInt(1))
                         else $Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int)))), 
                (lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  $IsBox($l#4#x#0, TInt)
                     && 
                    LitInt(0) <= $Unbox($l#4#x#0): int
                     && $Unbox($l#4#x#0): int < Seq#Length(g#0)), 
                (lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  SetRef_to_SetBox((lambda $l#4#o#0: ref :: false))))), 
            $LS($LZ))));
    g'#0 := _module.__default.SeqInit(TInt, 
      Seq#Length(g#0), 
      Lit(AtLayer((lambda $l#5#ly#0: LayerType :: 
            Handle1((lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                $Box((if $Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int == index#0
                     then _module.__default.unused()
                     else (if $Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int > index#0
                       then _module.__default.Sub($Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int, LitInt(1))
                       else $Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int)))), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                $IsBox($l#5#x#0, TInt)
                   && 
                  LitInt(0) <= $Unbox($l#5#x#0): int
                   && $Unbox($l#5#x#0): int < Seq#Length(g#0)), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#5#o#0: ref :: false))))), 
          $LS($LZ))));
    assume {:captureState "DLL_Dafny.dfy(258,82)"} true;
}



procedure CheckWellformed$$_module.__default.Remove(_module._default.Remove$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Remove$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Remove$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int)
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Remove$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Remove$A), $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Remove(_module._default.Remove$A: Ty, l#0: DatatypeType, p#0: int)
   returns (l'#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var ##l#2: DatatypeType;
  var ##l#3: DatatypeType;
  var ##l#4: DatatypeType;
  var ##l#5: DatatypeType;
  var ##p#1: int;
  var ##s#0: Seq Box;
  var ##k#0: int;
  var x#0: int;
  var ##l#6: DatatypeType;
  var ##p#2: int;
  var ##l#7: DatatypeType;
  var ##p#3: int;
  var ##l#8: DatatypeType;
  var ##p#4: int;
  var ##l#9: DatatypeType;
  var ##p#5: int;
  var ##l#10: DatatypeType;
  var ##p#6: int;
  var ##l#11: DatatypeType;
  var ##p#7: int;
  var ##l#12: DatatypeType;
  var ##p#8: int;
  var ##l#13: DatatypeType;
  var ##p#9: int;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: Remove, CheckWellformed$$_module.__default.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(262,7): initial state"} true;
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.Remove$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.Remove$A, l#0);
    assume _module.__default.Inv(_module._default.Remove$A, l#0);
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.Remove$A), $Heap);
    ##p#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#0, TInt, $Heap);
    assume _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, p#0);
    assume _module.__default.ValidPtr(_module._default.Remove$A, l#0, p#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc l'#0;
    assume {:captureState "DLL_Dafny.dfy(265,13): post-state"} true;
    ##l#2 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.Remove$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.Remove$A, l'#0);
    assume _module.__default.Inv(_module._default.Remove$A, l'#0);
    ##l#3 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.Remove$A), $Heap);
    assume _module.__default.Seq#canCall(_module._default.Remove$A, l'#0);
    ##l#4 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#4, Tclass._module.DList(_module._default.Remove$A), $Heap);
    assume _module.__default.Seq#canCall(_module._default.Remove$A, l#0);
    ##l#5 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#5, Tclass._module.DList(_module._default.Remove$A), $Heap);
    ##p#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#1, TInt, $Heap);
    assume _module.__default.Index#canCall(_module._default.Remove$A, l#0, p#0);
    ##s#0 := _module.__default.Seq(_module._default.Remove$A, l#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(_module._default.Remove$A), $Heap);
    ##k#0 := _module.__default.Index(_module._default.Remove$A, l#0, p#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#0;
    assert {:subsumption 0} ##k#0 < Seq#Length(##s#0);
    assume LitInt(0) <= ##k#0 && ##k#0 < Seq#Length(##s#0);
    assume _module.__default.SeqRemove#canCall(_module._default.Remove$A, 
      _module.__default.Seq(_module._default.Remove$A, l#0), 
      _module.__default.Index(_module._default.Remove$A, l#0, p#0));
    assume Seq#Equal(_module.__default.Seq(_module._default.Remove$A, l'#0), 
      _module.__default.SeqRemove(_module._default.Remove$A, 
        _module.__default.Seq(_module._default.Remove$A, l#0), 
        _module.__default.Index(_module._default.Remove$A, l#0, p#0)));
    havoc x#0;
    if (*)
    {
        assume x#0 != p#0;
        ##l#6 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#6, Tclass._module.DList(_module._default.Remove$A), $Heap);
        ##p#2 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#2, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, x#0);
        assume _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#0);
        ##l#7 := l'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#7, Tclass._module.DList(_module._default.Remove$A), $Heap);
        ##p#3 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#3, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.Remove$A, l'#0, x#0);
        assume _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#0);
        if (*)
        {
            ##l#8 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#8, Tclass._module.DList(_module._default.Remove$A), $Heap);
            ##p#4 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#4, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#0);
            ##l#9 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#9, Tclass._module.DList(_module._default.Remove$A), $Heap);
            ##p#5 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#5, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Remove$A, l#0, p#0);
            assume _module.__default.Index(_module._default.Remove$A, l#0, x#0)
               < _module.__default.Index(_module._default.Remove$A, l#0, p#0);
            ##l#10 := l'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#10, Tclass._module.DList(_module._default.Remove$A), $Heap);
            ##p#6 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#6, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Remove$A, l'#0, x#0);
            ##l#11 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#11, Tclass._module.DList(_module._default.Remove$A), $Heap);
            ##p#7 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#7, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#0);
            assume _module.__default.Index(_module._default.Remove$A, l'#0, x#0)
               == _module.__default.Index(_module._default.Remove$A, l#0, x#0);
        }
        else
        {
            assume _module.__default.Index(_module._default.Remove$A, l#0, p#0)
               <= _module.__default.Index(_module._default.Remove$A, l#0, x#0);
            ##l#12 := l'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#12, Tclass._module.DList(_module._default.Remove$A), $Heap);
            ##p#8 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#8, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Remove$A, l'#0, x#0);
            ##l#13 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#13, Tclass._module.DList(_module._default.Remove$A), $Heap);
            ##p#9 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#9, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#0);
            ##a#0 := _module.__default.Index(_module._default.Remove$A, l#0, x#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, TInt, $Heap);
            ##b#0 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assume _module.__default.Sub#canCall(_module.__default.Index(_module._default.Remove$A, l#0, x#0), LitInt(1));
            assume _module.__default.Index(_module._default.Remove$A, l'#0, x#0)
               == _module.__default.Sub(_module.__default.Index(_module._default.Remove$A, l#0, x#0), LitInt(1));
        }
    }
    else
    {
        assume x#0 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#0)
           ==> _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#0)
             && (if _module.__default.Index(_module._default.Remove$A, l#0, x#0)
                 < _module.__default.Index(_module._default.Remove$A, l#0, p#0)
               then _module.__default.Index(_module._default.Remove$A, l'#0, x#0)
                 == _module.__default.Index(_module._default.Remove$A, l#0, x#0)
               else _module.__default.Index(_module._default.Remove$A, l'#0, x#0)
                 == _module.__default.Sub(_module.__default.Index(_module._default.Remove$A, l#0, x#0), LitInt(1)));
    }

    assume (forall x#1: int :: 
      { _module.__default.Index(_module._default.Remove$A, l'#0, x#1) } 
        { _module.__default.Index(_module._default.Remove$A, l#0, x#1) } 
        { _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1) } 
        { _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1) } 
      true
         ==> (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
             ==> _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1))
           && (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
             ==> (if _module.__default.Index(_module._default.Remove$A, l#0, x#1)
                 < _module.__default.Index(_module._default.Remove$A, l#0, p#0)
               then _module.__default.Index(_module._default.Remove$A, l'#0, x#1)
                 == _module.__default.Index(_module._default.Remove$A, l#0, x#1)
               else _module.__default.Index(_module._default.Remove$A, l'#0, x#1)
                 == _module.__default.Sub(_module.__default.Index(_module._default.Remove$A, l#0, x#1), LitInt(1)))));
}



procedure Call$$_module.__default.Remove(_module._default.Remove$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Remove$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Remove$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int)
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Remove$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Remove$A), $Heap));
  // user-defined preconditions
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.f(l#0)) == Seq#Length(_module.DList.s(l#0)));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.g(l#0)) == Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.nodes(l#0)) > 0);
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || $Unbox(Seq#Index(_module.DList.g(l#0), LitInt(0))): int
             == _module.__default.sentinel());
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || LitInt(0) <= _module.DList.freeStack(l#0));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || _module.DList.freeStack(l#0) < Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#0: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int } 
            true
               ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int)
                 && (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int
                     < Seq#Length(_module.DList.nodes(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#1: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#1 && i#1 < Seq#Length(_module.DList.f(l#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int
                 == i#1));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#1: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int } 
            true
               ==> (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int)
                 && (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int
                     < Seq#Length(_module.DList.s(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#2: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#2 && p#2 < Seq#Length(_module.DList.g(l#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType))
                 && (LitInt(0) <= p#2 && p#2 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType)
                     < Seq#Length(_module.DList.g(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#3: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#3)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#3 && p#3 < Seq#Length(_module.DList.g(l#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#3)): DatatypeType)))));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#4: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int } 
            true
               ==> 
              LitInt(0) <= p#4
                 && p#4 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
                 == _module.__default.sentinel()
               ==> p#4 == LitInt(0)));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#5: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)): int } 
              { Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int) } 
            true
               ==> 
              LitInt(0) <= p#5
                 && p#5 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)): int
                   == p#5
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#5)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)))));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#6: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#6
                 && p#6 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l#0))
                   then $Unbox(Seq#Index(_module.DList.f(l#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int, LitInt(1)))): int
                   else 0)));
  requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#7)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#7
                     && p#7 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int
                   ==> true)
                 && (LitInt(0) <= p#7
                     && p#7 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#7)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l#0)), LitInt(1)))): int)))));
  requires _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, p#0)
     ==> _module.__default.ValidPtr(_module._default.Remove$A, l#0, p#0) || 0 < p#0;
  requires _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, p#0)
     ==> _module.__default.ValidPtr(_module._default.Remove$A, l#0, p#0)
       || p#0 < Seq#Length(_module.DList.g(l#0));
  requires _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, p#0)
     ==> _module.__default.ValidPtr(_module._default.Remove$A, l#0, p#0)
       || $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int >= LitInt(0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0);
  free ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     && 
    _module.__default.Inv(_module._default.Remove$A, l'#0)
     && $Is(_module.DList.nodes(l'#0), TSeq(Tclass._module.Node(_module._default.Remove$A)))
     && $Is(_module.DList.s(l'#0), TSeq(_module._default.Remove$A))
     && $Is(_module.DList.f(l'#0), TSeq(TInt))
     && $Is(_module.DList.g(l'#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.Remove$A, 
      _module.DList.nodes(l'#0), 
      _module.DList.freeStack(l'#0), 
      _module.DList.s(l'#0), 
      _module.DList.f(l'#0), 
      _module.DList.g(l'#0));
  free ensures _module.__default.Seq#canCall(_module._default.Remove$A, l'#0)
     && 
    _module.__default.Seq#canCall(_module._default.Remove$A, l#0)
     && _module.__default.Index#canCall(_module._default.Remove$A, l#0, p#0)
     && _module.__default.SeqRemove#canCall(_module._default.Remove$A, 
      _module.__default.Seq(_module._default.Remove$A, l#0), 
      _module.__default.Index(_module._default.Remove$A, l#0, p#0));
  ensures Seq#Equal(_module.__default.Seq(_module._default.Remove$A, l'#0), 
    _module.__default.SeqRemove(_module._default.Remove$A, 
      _module.__default.Seq(_module._default.Remove$A, l#0), 
      _module.__default.Index(_module._default.Remove$A, l#0, p#0)));
  free ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.Remove$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1) } 
    (x#1 != p#0
         ==> _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
             ==> _module.__default.ValidPtr#canCall(_module._default.Remove$A, l'#0, x#1)))
       && (
        (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1))
         ==> 
        x#1 != p#0
         ==> _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
             ==> _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#1)
               && _module.__default.Index#canCall(_module._default.Remove$A, l#0, p#0)
               && (_module.__default.Index(_module._default.Remove$A, l#0, x#1)
                   < _module.__default.Index(_module._default.Remove$A, l#0, p#0)
                 ==> _module.__default.Index#canCall(_module._default.Remove$A, l'#0, x#1)
                   && _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#1))
               && (_module.__default.Index(_module._default.Remove$A, l#0, p#0)
                   <= _module.__default.Index(_module._default.Remove$A, l#0, x#1)
                 ==> _module.__default.Index#canCall(_module._default.Remove$A, l'#0, x#1)
                   && 
                  _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#1)
                   && _module.__default.Sub#canCall(_module.__default.Index(_module._default.Remove$A, l#0, x#1), LitInt(1))))));
  ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.Remove$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1) } 
    true
       ==> (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1))
         && (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
           ==> (if _module.__default.Index(_module._default.Remove$A, l#0, x#1)
               < _module.__default.Index(_module._default.Remove$A, l#0, p#0)
             then _module.__default.Index(_module._default.Remove$A, l'#0, x#1)
               == _module.__default.Index(_module._default.Remove$A, l#0, x#1)
             else _module.__default.Index(_module._default.Remove$A, l'#0, x#1)
               == _module.__default.Sub(_module.__default.Index(_module._default.Remove$A, l#0, x#1), LitInt(1)))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Remove(_module._default.Remove$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Remove$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Remove$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int)
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Remove$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Remove$A), $Heap), 
    $_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Inv#canCall(_module._default.Remove$A, l#0)
     && 
    _module.__default.Inv(_module._default.Remove$A, l#0)
     && $Is(_module.DList.nodes(l#0), TSeq(Tclass._module.Node(_module._default.Remove$A)))
     && $Is(_module.DList.s(l#0), TSeq(_module._default.Remove$A))
     && $Is(_module.DList.f(l#0), TSeq(TInt))
     && $Is(_module.DList.g(l#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.Remove$A, 
      _module.DList.nodes(l#0), 
      _module.DList.freeStack(l#0), 
      _module.DList.s(l#0), 
      _module.DList.f(l#0), 
      _module.DList.g(l#0));
  free requires _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, p#0)
     && 
    _module.__default.ValidPtr(_module._default.Remove$A, l#0, p#0)
     && 
    0 < p#0
     && p#0 < Seq#Length(_module.DList.g(l#0))
     && $Unbox(Seq#Index(_module.DList.g(l#0), p#0)): int >= LitInt(0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0);
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.f(l'#0)) == Seq#Length(_module.DList.s(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.g(l'#0)) == Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.nodes(l'#0)) > 0);
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || $Unbox(Seq#Index(_module.DList.g(l'#0), LitInt(0))): int
             == _module.__default.sentinel());
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || LitInt(0) <= _module.DList.freeStack(l'#0));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || _module.DList.freeStack(l'#0) < Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#6: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int
                     < Seq#Length(_module.DList.nodes(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(_module.DList.f(l'#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int
                 == i#7));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#22: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int } 
            true
               ==> (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.__default.unused()
                     <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int)
                 && (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int
                     < Seq#Length(_module.DList.s(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#23: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#23 && p#23 < Seq#Length(_module.DList.g(l'#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType))
                 && (LitInt(0) <= p#23 && p#23 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType)
                     < Seq#Length(_module.DList.g(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#24: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#24)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#24 && p#24 < Seq#Length(_module.DList.g(l'#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#24)): DatatypeType)))));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#25: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int } 
            true
               ==> 
              LitInt(0) <= p#25
                 && p#25 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
                 == _module.__default.sentinel()
               ==> p#25 == LitInt(0)));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#26: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)): int } 
              { Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int) } 
            true
               ==> 
              LitInt(0) <= p#26
                 && p#26 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)): int
                   == p#26
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#26)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)))));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#27: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#27
                 && p#27 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l'#0))
                   then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int, LitInt(1)))): int
                   else 0)));
  ensures _module.__default.Inv#canCall(_module._default.Remove$A, l'#0)
     ==> _module.__default.Inv(_module._default.Remove$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.Remove$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.Remove$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#28: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#28)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#28
                     && p#28 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int
                   ==> true)
                 && (LitInt(0) <= p#28
                     && p#28 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#28)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l'#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l'#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l'#0)), LitInt(1)))): int)))));
  free ensures _module.__default.Seq#canCall(_module._default.Remove$A, l'#0)
     && 
    _module.__default.Seq#canCall(_module._default.Remove$A, l#0)
     && _module.__default.Index#canCall(_module._default.Remove$A, l#0, p#0)
     && _module.__default.SeqRemove#canCall(_module._default.Remove$A, 
      _module.__default.Seq(_module._default.Remove$A, l#0), 
      _module.__default.Index(_module._default.Remove$A, l#0, p#0));
  ensures Seq#Equal(_module.__default.Seq(_module._default.Remove$A, l'#0), 
    _module.__default.SeqRemove(_module._default.Remove$A, 
      _module.__default.Seq(_module._default.Remove$A, l#0), 
      _module.__default.Index(_module._default.Remove$A, l#0, p#0)));
  free ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.Remove$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1) } 
    (x#1 != p#0
         ==> _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
             ==> _module.__default.ValidPtr#canCall(_module._default.Remove$A, l'#0, x#1)))
       && (
        (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1))
         ==> 
        x#1 != p#0
         ==> _module.__default.ValidPtr#canCall(_module._default.Remove$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
             ==> _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#1)
               && _module.__default.Index#canCall(_module._default.Remove$A, l#0, p#0)
               && (_module.__default.Index(_module._default.Remove$A, l#0, x#1)
                   < _module.__default.Index(_module._default.Remove$A, l#0, p#0)
                 ==> _module.__default.Index#canCall(_module._default.Remove$A, l'#0, x#1)
                   && _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#1))
               && (_module.__default.Index(_module._default.Remove$A, l#0, p#0)
                   <= _module.__default.Index(_module._default.Remove$A, l#0, x#1)
                 ==> _module.__default.Index#canCall(_module._default.Remove$A, l'#0, x#1)
                   && 
                  _module.__default.Index#canCall(_module._default.Remove$A, l#0, x#1)
                   && _module.__default.Sub#canCall(_module.__default.Index(_module._default.Remove$A, l#0, x#1), LitInt(1))))));
  ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.Remove$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1) } 
    true
       ==> (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.Remove$A, l'#0, x#1))
         && (x#1 != p#0 && _module.__default.ValidPtr(_module._default.Remove$A, l#0, x#1)
           ==> (if _module.__default.Index(_module._default.Remove$A, l#0, x#1)
               < _module.__default.Index(_module._default.Remove$A, l#0, p#0)
             then _module.__default.Index(_module._default.Remove$A, l'#0, x#1)
               == _module.__default.Index(_module._default.Remove$A, l#0, x#1)
             else _module.__default.Index(_module._default.Remove$A, l'#0, x#1)
               == _module.__default.Sub(_module.__default.Index(_module._default.Remove$A, l#0, x#1), LitInt(1)))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Remove(_module._default.Remove$A: Ty, l#0: DatatypeType, p#0: int)
   returns (l'#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var nodes#0: Seq Box;
  var freeStack#0: int;
  var s#0: Seq Box;
  var f#0: Seq Box;
  var g#0: Seq Box;
  var let#0#0#0: DatatypeType;
  var index#0: int;
  var s'#0: Seq Box
     where $Is(s'#0, TSeq(_module._default.Remove$A))
       && $IsAlloc(s'#0, TSeq(_module._default.Remove$A), $Heap);
  var ##s#1: Seq Box;
  var ##k#1: int;
  var f'#0: Seq Box where $Is(f'#0, TSeq(TInt)) && $IsAlloc(f'#0, TSeq(TInt), $Heap);
  var ##s#2: Seq Box;
  var ##k#2: int;
  var g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap);
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var g##0: Seq Box;
  var index##0: int;
  var node#0: DatatypeType
     where $Is(node#0, Tclass._module.Node(_module._default.Remove$A))
       && $IsAlloc(node#0, Tclass._module.Node(_module._default.Remove$A), $Heap);
  var ##s#3: Seq Box;
  var ##i#0: int;
  var node_prev#0: DatatypeType
     where $Is(node_prev#0, Tclass._module.Node(_module._default.Remove$A))
       && $IsAlloc(node_prev#0, Tclass._module.Node(_module._default.Remove$A), $Heap);
  var ##s#4: Seq Box;
  var ##i#1: int;
  var dt_update_tmp#0#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var dt_update#next#0#0: int;
  var let#2#0#0: int;
  var ##s1#0: Seq Box;
  var ##i#2: int;
  var ##a#1: DatatypeType;
  var node_next#0: DatatypeType
     where $Is(node_next#0, Tclass._module.Node(_module._default.Remove$A))
       && $IsAlloc(node_next#0, Tclass._module.Node(_module._default.Remove$A), $Heap);
  var ##s#5: Seq Box;
  var ##i#3: int;
  var dt_update_tmp#1#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var dt_update#prev#0#0: int;
  var let#4#0#0: int;
  var ##s1#1: Seq Box;
  var ##i#4: int;
  var ##a#2: DatatypeType;
  var ##s1#2: Seq Box;
  var ##i#5: int;
  var ##a#3: DatatypeType;

    // AddMethodImpl: Remove, Impl$$_module.__default.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(271,0): initial state"} true;
    $_reverifyPost := false;
    havoc nodes#0;
    assume $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Remove$A)))
       && $IsAlloc(nodes#0, TSeq(Tclass._module.Node(_module._default.Remove$A)), $Heap);
    havoc freeStack#0;
    havoc s#0;
    assume $Is(s#0, TSeq(_module._default.Remove$A))
       && $IsAlloc(s#0, TSeq(_module._default.Remove$A), $Heap);
    havoc f#0;
    assume $Is(f#0, TSeq(TInt)) && $IsAlloc(f#0, TSeq(TInt), $Heap);
    havoc g#0;
    assume $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap);
    assume let#0#0#0 == l#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.DList(_module._default.Remove$A));
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume #_module.DList.DList(nodes#0, freeStack#0, s#0, f#0, g#0) == let#0#0#0;
    // ----- assignment statement ----- DLL_Dafny.dfy(275,19)
    assume true;
    assert 0 <= p#0 && p#0 < Seq#Length(g#0);
    assume true;
    index#0 := $Unbox(Seq#Index(g#0, p#0)): int;
    assume {:captureState "DLL_Dafny.dfy(275,25)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(276,16)
    assume true;
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, TSeq(_module._default.Remove$A), $Heap);
    ##k#1 := index#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#1;
    assert {:subsumption 0} ##k#1 < Seq#Length(##s#1);
    assume LitInt(0) <= ##k#1 && ##k#1 < Seq#Length(##s#1);
    assume _module.__default.SeqRemove#canCall(_module._default.Remove$A, s#0, index#0);
    assume _module.__default.SeqRemove#canCall(_module._default.Remove$A, s#0, index#0);
    s'#0 := _module.__default.SeqRemove(_module._default.Remove$A, s#0, index#0);
    assume {:captureState "DLL_Dafny.dfy(276,37)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(277,16)
    assume true;
    ##s#2 := f#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, TSeq(TInt), $Heap);
    ##k#2 := index#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#2, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#2;
    assert {:subsumption 0} ##k#2 < Seq#Length(##s#2);
    assume LitInt(0) <= ##k#2 && ##k#2 < Seq#Length(##s#2);
    assume _module.__default.SeqRemove#canCall(TInt, f#0, index#0);
    assume _module.__default.SeqRemove#canCall(TInt, f#0, index#0);
    f'#0 := _module.__default.SeqRemove(TInt, f#0, index#0);
    assume {:captureState "DLL_Dafny.dfy(277,37)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(278,33)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type seq<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    g##0 := g#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    index##0 := index#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.Remove__SeqInit(g##0, index##0);
    // TrCallStmt: After ProcessCallStmt
    g'#0 := $rhs##0;
    assume {:captureState "DLL_Dafny.dfy(278,42)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(279,12)
    assume true;
    ##s#3 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, TSeq(Tclass._module.Node(_module._default.Remove$A)), $Heap);
    ##i#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#0;
    assert {:subsumption 0} ##i#0 < Seq#Length(##s#3);
    assume LitInt(0) <= ##i#0 && ##i#0 < Seq#Length(##s#3);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Remove$A), nodes#0, p#0);
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Remove$A), nodes#0, p#0)): DatatypeType);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Remove$A), nodes#0, p#0);
    node#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Remove$A), nodes#0, p#0)): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(279,31)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(280,17)
    assume true;
    assume _module.Node.Node_q(node#0);
    ##s#4 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#4, TSeq(Tclass._module.Node(_module._default.Remove$A)), $Heap);
    ##i#1 := _module.Node.prev(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#1;
    assert {:subsumption 0} ##i#1 < Seq#Length(##s#4);
    assume LitInt(0) <= ##i#1 && ##i#1 < Seq#Length(##s#4);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      _module.Node.prev(node#0));
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Remove$A), 
          nodes#0, 
          _module.Node.prev(node#0))): DatatypeType);
    assume _module.Node.Node_q(node#0)
       && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Remove$A), 
        nodes#0, 
        _module.Node.prev(node#0));
    node_prev#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Remove$A), 
        nodes#0, 
        _module.Node.prev(node#0))): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(280,44)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(281,9)
    assume true;
    assume _module.Node.Node_q(node#0);
    havoc dt_update_tmp#0#0;
    assume $Is(dt_update_tmp#0#0, Tclass._module.Node(_module._default.Remove$A));
    assume let#1#0#0 == node_prev#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, Tclass._module.Node(_module._default.Remove$A));
    assume dt_update_tmp#0#0 == let#1#0#0;
    havoc dt_update#next#0#0;
    assume _module.Node.Node_q(node#0);
    assume let#2#0#0 == _module.Node.next(node#0);
    assume _module.Node.Node_q(node#0);
    // CheckWellformedWithResult: any expression
    assume $Is(let#2#0#0, TInt);
    assume dt_update#next#0#0 == let#2#0#0;
    assume _module.Node.Node_q(dt_update_tmp#0#0);
    assume _module.Node.Node_q(dt_update_tmp#0#0);
    ##s1#0 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#0, TSeq(Tclass._module.Node(_module._default.Remove$A)), $Heap);
    ##i#2 := _module.Node.prev(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#2, TInt, $Heap);
    ##a#1 := (var dt_update_tmp#0#1 := node_prev#0; 
      (var dt_update#next#0#1 := _module.Node.next(node#0); 
        #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
          dt_update#next#0#1, 
          _module.Node.prev(dt_update_tmp#0#1))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, Tclass._module.Node(_module._default.Remove$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#2;
    assert {:subsumption 0} ##i#2 < Seq#Length(##s1#0);
    assume LitInt(0) <= ##i#2 && ##i#2 < Seq#Length(##s1#0);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      _module.Node.prev(node#0), 
      $Box((var dt_update_tmp#0#1 := node_prev#0; 
          (var dt_update#next#0#1 := _module.Node.next(node#0); 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
              dt_update#next#0#1, 
              _module.Node.prev(dt_update_tmp#0#1))))));
    assume _module.Node.Node_q(node#0)
       && (var dt_update_tmp#0#1 := node_prev#0; 
        _module.Node.Node_q(node#0)
           && 
          _module.Node.Node_q(dt_update_tmp#0#1)
           && _module.Node.Node_q(dt_update_tmp#0#1))
       && _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.Remove$A), 
        nodes#0, 
        _module.Node.prev(node#0), 
        $Box((var dt_update_tmp#0#1 := node_prev#0; 
            (var dt_update#next#0#1 := _module.Node.next(node#0); 
              #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
                dt_update#next#0#1, 
                _module.Node.prev(dt_update_tmp#0#1))))));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      _module.Node.prev(node#0), 
      $Box((var dt_update_tmp#0#1 := node_prev#0; 
          (var dt_update#next#0#1 := _module.Node.next(node#0); 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
              dt_update#next#0#1, 
              _module.Node.prev(dt_update_tmp#0#1))))));
    assume {:captureState "DLL_Dafny.dfy(281,67)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(282,17)
    assume true;
    assume _module.Node.Node_q(node#0);
    ##s#5 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#5, TSeq(Tclass._module.Node(_module._default.Remove$A)), $Heap);
    ##i#3 := _module.Node.next(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#3;
    assert {:subsumption 0} ##i#3 < Seq#Length(##s#5);
    assume LitInt(0) <= ##i#3 && ##i#3 < Seq#Length(##s#5);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      _module.Node.next(node#0));
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Remove$A), 
          nodes#0, 
          _module.Node.next(node#0))): DatatypeType);
    assume _module.Node.Node_q(node#0)
       && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.Remove$A), 
        nodes#0, 
        _module.Node.next(node#0));
    node_next#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.Remove$A), 
        nodes#0, 
        _module.Node.next(node#0))): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(282,44)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(283,9)
    assume true;
    assume _module.Node.Node_q(node#0);
    havoc dt_update_tmp#1#0;
    assume $Is(dt_update_tmp#1#0, Tclass._module.Node(_module._default.Remove$A));
    assume let#3#0#0 == node_next#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#3#0#0, Tclass._module.Node(_module._default.Remove$A));
    assume dt_update_tmp#1#0 == let#3#0#0;
    havoc dt_update#prev#0#0;
    assume _module.Node.Node_q(node#0);
    assume let#4#0#0 == _module.Node.prev(node#0);
    assume _module.Node.Node_q(node#0);
    // CheckWellformedWithResult: any expression
    assume $Is(let#4#0#0, TInt);
    assume dt_update#prev#0#0 == let#4#0#0;
    assume _module.Node.Node_q(dt_update_tmp#1#0);
    assume _module.Node.Node_q(dt_update_tmp#1#0);
    ##s1#1 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#1, TSeq(Tclass._module.Node(_module._default.Remove$A)), $Heap);
    ##i#4 := _module.Node.next(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#4, TInt, $Heap);
    ##a#2 := (var dt_update_tmp#1#1 := node_next#0; 
      (var dt_update#prev#0#1 := _module.Node.prev(node#0); 
        #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
          _module.Node.next(dt_update_tmp#1#1), 
          dt_update#prev#0#1)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, Tclass._module.Node(_module._default.Remove$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#4;
    assert {:subsumption 0} ##i#4 < Seq#Length(##s1#1);
    assume LitInt(0) <= ##i#4 && ##i#4 < Seq#Length(##s1#1);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      _module.Node.next(node#0), 
      $Box((var dt_update_tmp#1#1 := node_next#0; 
          (var dt_update#prev#0#1 := _module.Node.prev(node#0); 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
              _module.Node.next(dt_update_tmp#1#1), 
              dt_update#prev#0#1)))));
    assume _module.Node.Node_q(node#0)
       && (var dt_update_tmp#1#1 := node_next#0; 
        _module.Node.Node_q(node#0)
           && 
          _module.Node.Node_q(dt_update_tmp#1#1)
           && _module.Node.Node_q(dt_update_tmp#1#1))
       && _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.Remove$A), 
        nodes#0, 
        _module.Node.next(node#0), 
        $Box((var dt_update_tmp#1#1 := node_next#0; 
            (var dt_update#prev#0#1 := _module.Node.prev(node#0); 
              #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
                _module.Node.next(dt_update_tmp#1#1), 
                dt_update#prev#0#1)))));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      _module.Node.next(node#0), 
      $Box((var dt_update_tmp#1#1 := node_next#0; 
          (var dt_update#prev#0#1 := _module.Node.prev(node#0); 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
              _module.Node.next(dt_update_tmp#1#1), 
              dt_update#prev#0#1)))));
    assume {:captureState "DLL_Dafny.dfy(283,67)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(284,9)
    assume true;
    ##s1#2 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#2, TSeq(Tclass._module.Node(_module._default.Remove$A)), $Heap);
    ##i#5 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#5, TInt, $Heap);
    ##a#3 := #_module.Node.Node(Lit(#_module.Option.None()), freeStack#0, LitInt(0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, Tclass._module.Node(_module._default.Remove$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#5;
    assert {:subsumption 0} ##i#5 < Seq#Length(##s1#2);
    assume LitInt(0) <= ##i#5 && ##i#5 < Seq#Length(##s1#2);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      p#0, 
      $Box(#_module.Node.Node(Lit(#_module.Option.None()), freeStack#0, LitInt(0))));
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      p#0, 
      $Box(#_module.Node.Node(Lit(#_module.Option.None()), freeStack#0, LitInt(0))));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.Remove$A), 
      nodes#0, 
      p#0, 
      $Box(#_module.Node.Node(Lit(#_module.Option.None()), freeStack#0, LitInt(0))));
    assume {:captureState "DLL_Dafny.dfy(284,54)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(285,6)
    assume true;
    assume true;
    l'#0 := #_module.DList.DList(nodes#0, p#0, s'#0, f'#0, g'#0);
    assume {:captureState "DLL_Dafny.dfy(285,35)"} true;
}



procedure CheckWellformed$$_module.__default.InsertAfter__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    p'#0: int, 
    index#0: int, 
    index'#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InsertAfter__SeqInit(g#0: Seq Box, p'#0: int, index#0: int, index'#0: int) returns (g'#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: InsertAfter_SeqInit, CheckWellformed$$_module.__default.InsertAfter__SeqInit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(288,13): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc g'#0;
    assume {:captureState "DLL_Dafny.dfy(289,15): post-state"} true;
    assume Seq#Length(g'#0) == Seq#Length(g#0);
    havoc x#0;
    if (*)
    {
        assume LitInt(0) <= x#0;
        assume x#0 < Seq#Length(g#0);
        if (*)
        {
            assume x#0 == p'#0;
            assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
            assume $Unbox(Seq#Index(g'#0, x#0)): int == index'#0;
        }
        else
        {
            assume x#0 != p'#0;
            if (*)
            {
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                assume index#0 < $Unbox(Seq#Index(g#0, x#0)): int;
                assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                ##a#0 := $Unbox(Seq#Index(g#0, x#0)): int;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, TInt, $Heap);
                ##b#0 := LitInt(1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, TInt, $Heap);
                assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1));
                assume $Unbox(Seq#Index(g'#0, x#0)): int
                   == _module.__default.Add($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1));
            }
            else
            {
                assume $Unbox(Seq#Index(g#0, x#0)): int <= index#0;
                assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                assume $Unbox(Seq#Index(g'#0, x#0)): int == $Unbox(Seq#Index(g#0, x#0)): int;
            }
        }
    }
    else
    {
        assume LitInt(0) <= x#0 && x#0 < Seq#Length(g#0)
           ==> (if x#0 == p'#0
             then $Unbox(Seq#Index(g'#0, x#0)): int == index'#0
             else (if index#0 < $Unbox(Seq#Index(g#0, x#0)): int
               then $Unbox(Seq#Index(g'#0, x#0)): int
                 == _module.__default.Add($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1))
               else $Unbox(Seq#Index(g'#0, x#0)): int == $Unbox(Seq#Index(g#0, x#0)): int));
    }

    assume (forall x#1: int :: 
      { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
      true
         ==> 
        LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
         ==> (if x#1 == p'#0
           then $Unbox(Seq#Index(g'#0, x#1)): int == index'#0
           else (if index#0 < $Unbox(Seq#Index(g#0, x#1)): int
             then $Unbox(Seq#Index(g'#0, x#1)): int
               == _module.__default.Add($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
             else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
}



procedure Call$$_module.__default.InsertAfter__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    p'#0: int, 
    index#0: int, 
    index'#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(g'#0) == Seq#Length(g#0);
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> 
      x#1 != p'#0
       ==> 
      index#0 < $Unbox(Seq#Index(g#0, x#1)): int
       ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1)));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    true
       ==> 
      LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> (if x#1 == p'#0
         then $Unbox(Seq#Index(g'#0, x#1)): int == index'#0
         else (if index#0 < $Unbox(Seq#Index(g#0, x#1)): int
           then $Unbox(Seq#Index(g'#0, x#1)): int
             == _module.__default.Add($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
           else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.InsertAfter__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    p'#0: int, 
    index#0: int, 
    index'#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(g'#0) == Seq#Length(g#0);
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> 
      x#1 != p'#0
       ==> 
      index#0 < $Unbox(Seq#Index(g#0, x#1)): int
       ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1)));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    true
       ==> 
      LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> (if x#1 == p'#0
         then $Unbox(Seq#Index(g'#0, x#1)): int == index'#0
         else (if index#0 < $Unbox(Seq#Index(g#0, x#1)): int
           then $Unbox(Seq#Index(g'#0, x#1)): int
             == _module.__default.Add($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
           else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.InsertAfter__SeqInit(g#0: Seq Box, p'#0: int, index#0: int, index'#0: int)
   returns (g'#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: int;
  var ##a#1: int;
  var ##b#1: int;
  var ##len#0: int;
  var ##func#0: HandleType;

    // AddMethodImpl: InsertAfter_SeqInit, Impl$$_module.__default.InsertAfter__SeqInit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(295,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- DLL_Dafny.dfy(296,8)
    assume true;
    havoc x#2;
    // Begin Comprehension WF check
    if (*)
    {
        $oldHeap#0 := $Heap;
        havoc $Heap;
        assume $IsGoodHeap($Heap);
        assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
        $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (LitInt(0) <= x#2)
        {
        }

        if (LitInt(0) <= x#2 && x#2 < Seq#Length(g#0))
        {
            if (x#2 == p'#0)
            {
                assume lambdaResult#0 == index'#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, TInt);
            }
            else
            {
                assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                if (index#0 < $Unbox(Seq#Index(g#0, x#2)): int)
                {
                    assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                    ##a#1 := $Unbox(Seq#Index(g#0, x#2)): int;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##a#1, TInt, $Heap);
                    ##b#1 := LitInt(1);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##b#1, TInt, $Heap);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame#l0[$o, $f]);
                    assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    assume lambdaResult#0
                       == _module.__default.Add($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    // CheckWellformedWithResult: any expression
                    assume $Is(lambdaResult#0, TInt);
                }
                else
                {
                    assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                    assume lambdaResult#0 == $Unbox(Seq#Index(g#0, x#2)): int;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(lambdaResult#0, TInt);
                }
            }
        }

        assume false;
    }

    // End Comprehension WF check
    ##len#0 := Seq#Length(g#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##len#0, TInt, $Heap);
    ##func#0 := Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
          Handle1((lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              $Box((if $Unbox($l#1#x#0): int == p'#0
                   then index'#0
                   else (if index#0 < $Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int
                     then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int, LitInt(1))
                     else $Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int)))), 
            (lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              $IsBox($l#1#x#0, TInt)
                 && 
                LitInt(0) <= $Unbox($l#1#x#0): int
                 && $Unbox($l#1#x#0): int < Seq#Length(g#0)), 
            (lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
        $LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##func#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap);
    assert {:subsumption 0} ##len#0 >= LitInt(0);
    assume ##len#0 >= LitInt(0);
    assert {:subsumption 0} (forall i#0: int :: 
      { Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)) } 
      true
         ==> 
        LitInt(0) <= i#0 && i#0 < ##len#0
         ==> Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)));
    assume (forall i#0: int :: 
      { Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)) } 
      true
         ==> 
        LitInt(0) <= i#0 && i#0 < ##len#0
         ==> Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)));
    assume _module.__default.SeqInit#canCall(TInt, 
      Seq#Length(g#0), 
      Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
            Handle1((lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                $Box((if $Unbox($l#2#x#0): int == p'#0
                     then index'#0
                     else (if index#0 < $Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int
                       then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int, LitInt(1))
                       else $Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int)))), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                $IsBox($l#2#x#0, TInt)
                   && 
                  LitInt(0) <= $Unbox($l#2#x#0): int
                   && $Unbox($l#2#x#0): int < Seq#Length(g#0)), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
          $LS($LZ))));
    assume (forall $l#3#x#0: int :: 
        LitInt(0) <= $l#3#x#0 && $l#3#x#0 < Seq#Length(g#0)
           ==> 
          $l#3#x#0 != p'#0
           ==> 
          index#0 < $Unbox(Seq#Index(g#0, $l#3#x#0)): int
           ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, $l#3#x#0)): int, LitInt(1)))
       && _module.__default.SeqInit#canCall(TInt, 
        Seq#Length(g#0), 
        Lit(AtLayer((lambda $l#4#ly#0: LayerType :: 
              Handle1((lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  $Box((if $Unbox($l#4#x#0): int == p'#0
                       then index'#0
                       else (if index#0 < $Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int
                         then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int, LitInt(1))
                         else $Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int)))), 
                (lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  $IsBox($l#4#x#0, TInt)
                     && 
                    LitInt(0) <= $Unbox($l#4#x#0): int
                     && $Unbox($l#4#x#0): int < Seq#Length(g#0)), 
                (lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  SetRef_to_SetBox((lambda $l#4#o#0: ref :: false))))), 
            $LS($LZ))));
    g'#0 := _module.__default.SeqInit(TInt, 
      Seq#Length(g#0), 
      Lit(AtLayer((lambda $l#5#ly#0: LayerType :: 
            Handle1((lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                $Box((if $Unbox($l#5#x#0): int == p'#0
                     then index'#0
                     else (if index#0 < $Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int
                       then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int, LitInt(1))
                       else $Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int)))), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                $IsBox($l#5#x#0, TInt)
                   && 
                  LitInt(0) <= $Unbox($l#5#x#0): int
                   && $Unbox($l#5#x#0): int < Seq#Length(g#0)), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#5#o#0: ref :: false))))), 
          $LS($LZ))));
    assume {:captureState "DLL_Dafny.dfy(297,78)"} true;
}



procedure CheckWellformed$$_module.__default.InsertAfter(_module._default.InsertAfter$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.InsertAfter$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.InsertAfter$A)
         && $IsAllocBox(a#0, _module._default.InsertAfter$A, $Heap))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.InsertAfter$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap), 
    p'#0: int);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InsertAfter(_module._default.InsertAfter$A: Ty, l#0: DatatypeType, p#0: int, a#0: Box)
   returns (l'#0: DatatypeType, p'#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var ##l#2: DatatypeType;
  var ##l#3: DatatypeType;
  var ##l#4: DatatypeType;
  var ##l#5: DatatypeType;
  var ##p#1: int;
  var ##a#0: int;
  var ##b#0: int;
  var ##s#0: Seq Box;
  var ##k#0: int;
  var ##v#0: Box;
  var ##l#6: DatatypeType;
  var ##p#2: int;
  var ##l#7: DatatypeType;
  var ##p#3: int;
  var ##l#8: DatatypeType;
  var ##p#4: int;
  var ##a#1: int;
  var ##b#1: int;
  var x#0: int;
  var ##l#9: DatatypeType;
  var ##p#5: int;
  var ##l#10: DatatypeType;
  var ##p#6: int;
  var ##l#11: DatatypeType;
  var ##p#7: int;
  var ##l#12: DatatypeType;
  var ##p#8: int;
  var ##l#13: DatatypeType;
  var ##p#9: int;
  var ##l#14: DatatypeType;
  var ##p#10: int;
  var ##l#15: DatatypeType;
  var ##p#11: int;
  var ##l#16: DatatypeType;
  var ##p#12: int;
  var ##a#2: int;
  var ##b#2: int;

    // AddMethodImpl: InsertAfter, CheckWellformed$$_module.__default.InsertAfter
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(301,7): initial state"} true;
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0);
    assume _module.__default.Inv(_module._default.InsertAfter$A, l#0);
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    ##p#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#0, TInt, $Heap);
    assume _module.__default.MaybePtr#canCall(_module._default.InsertAfter$A, l#0, p#0);
    assume _module.__default.MaybePtr(_module._default.InsertAfter$A, l#0, p#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc l'#0, p'#0;
    assume {:captureState "DLL_Dafny.dfy(304,13): post-state"} true;
    ##l#2 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0);
    assume _module.__default.Inv(_module._default.InsertAfter$A, l'#0);
    ##l#3 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    assume _module.__default.Seq#canCall(_module._default.InsertAfter$A, l'#0);
    ##l#4 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#4, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    assume _module.__default.Seq#canCall(_module._default.InsertAfter$A, l#0);
    ##l#5 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#5, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    ##p#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#1, TInt, $Heap);
    assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0);
    ##a#0 := _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TInt, $Heap);
    ##b#0 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assume _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1));
    ##s#0 := _module.__default.Seq(_module._default.InsertAfter$A, l#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(_module._default.InsertAfter$A), $Heap);
    ##k#0 := _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1));
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#0, TInt, $Heap);
    ##v#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##v#0, _module._default.InsertAfter$A, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#0;
    assert {:subsumption 0} ##k#0 <= Seq#Length(##s#0);
    assume LitInt(0) <= ##k#0 && ##k#0 <= Seq#Length(##s#0);
    assume _module.__default.SeqInsert#canCall(_module._default.InsertAfter$A, 
      _module.__default.Seq(_module._default.InsertAfter$A, l#0), 
      _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)), 
      a#0);
    assume Seq#Equal(_module.__default.Seq(_module._default.InsertAfter$A, l'#0), 
      _module.__default.SeqInsert(_module._default.InsertAfter$A, 
        _module.__default.Seq(_module._default.InsertAfter$A, l#0), 
        _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)), 
        a#0));
    ##l#6 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#6, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    ##p#2 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#2, TInt, $Heap);
    assume _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, p'#0);
    assume _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, p'#0);
    ##l#7 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#7, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    ##p#3 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#3, TInt, $Heap);
    assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, p'#0);
    ##l#8 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#8, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
    ##p#4 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#4, TInt, $Heap);
    assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0);
    ##a#1 := _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TInt, $Heap);
    ##b#1 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TInt, $Heap);
    assume _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1));
    assume _module.__default.Index(_module._default.InsertAfter$A, l'#0, p'#0)
       == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1));
    havoc x#0;
    if (*)
    {
        ##l#9 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#9, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
        ##p#5 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#5, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l#0, x#0);
        assume _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#0);
        ##l#10 := l'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#10, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
        ##p#6 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#6, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, x#0);
        assume _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#0);
        if (*)
        {
            ##l#11 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#11, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
            ##p#7 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#7, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#0);
            ##l#12 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#12, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
            ##p#8 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#8, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0);
            assume _module.__default.Index(_module._default.InsertAfter$A, l#0, x#0)
               <= _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0);
            ##l#13 := l'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#13, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
            ##p#9 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#9, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, x#0);
            ##l#14 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#14, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
            ##p#10 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#10, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#0);
            assume _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#0)
               == _module.__default.Index(_module._default.InsertAfter$A, l#0, x#0);
        }
        else
        {
            assume _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
               < _module.__default.Index(_module._default.InsertAfter$A, l#0, x#0);
            ##l#15 := l'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#15, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
            ##p#11 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#11, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, x#0);
            ##l#16 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#16, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
            ##p#12 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#12, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#0);
            ##a#2 := _module.__default.Index(_module._default.InsertAfter$A, l#0, x#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#2, TInt, $Heap);
            ##b#2 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assume _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#0), LitInt(1));
            assume _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#0)
               == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#0), LitInt(1));
        }
    }
    else
    {
        assume _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#0)
           ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#0)
             && (if _module.__default.Index(_module._default.InsertAfter$A, l#0, x#0)
                 <= _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
               then _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#0)
                 == _module.__default.Index(_module._default.InsertAfter$A, l#0, x#0)
               else _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#0)
                 == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#0), LitInt(1)));
    }

    assume (forall x#1: int :: 
      { _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1) } 
        { _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1) } 
        { _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1) } 
        { _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1) } 
      true
         ==> (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
             ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1))
           && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
             ==> (if _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
                 <= _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
               then _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1)
                 == _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
               else _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1)
                 == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#1), LitInt(1)))));
}



procedure Call$$_module.__default.InsertAfter(_module._default.InsertAfter$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.InsertAfter$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.InsertAfter$A)
         && $IsAllocBox(a#0, _module._default.InsertAfter$A, $Heap))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.InsertAfter$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap), 
    p'#0: int);
  // user-defined preconditions
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.f(l#0)) == Seq#Length(_module.DList.s(l#0)));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.g(l#0)) == Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.nodes(l#0)) > 0);
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || $Unbox(Seq#Index(_module.DList.g(l#0), LitInt(0))): int
             == _module.__default.sentinel());
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || LitInt(0) <= _module.DList.freeStack(l#0));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || _module.DList.freeStack(l#0) < Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#0: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int } 
            true
               ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int)
                 && (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int
                     < Seq#Length(_module.DList.nodes(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#1: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#1 && i#1 < Seq#Length(_module.DList.f(l#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int
                 == i#1));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#1: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int } 
            true
               ==> (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int)
                 && (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int
                     < Seq#Length(_module.DList.s(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#2: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#2 && p#2 < Seq#Length(_module.DList.g(l#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType))
                 && (LitInt(0) <= p#2 && p#2 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType)
                     < Seq#Length(_module.DList.g(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#3: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#3)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#3 && p#3 < Seq#Length(_module.DList.g(l#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#3)): DatatypeType)))));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#4: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int } 
            true
               ==> 
              LitInt(0) <= p#4
                 && p#4 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
                 == _module.__default.sentinel()
               ==> p#4 == LitInt(0)));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#5: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)): int } 
              { Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int) } 
            true
               ==> 
              LitInt(0) <= p#5
                 && p#5 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)): int
                   == p#5
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#5)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)))));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#6: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#6
                 && p#6 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l#0))
                   then $Unbox(Seq#Index(_module.DList.f(l#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int, LitInt(1)))): int
                   else 0)));
  requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#7)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#7
                     && p#7 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int
                   ==> true)
                 && (LitInt(0) <= p#7
                     && p#7 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#7)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l#0)), LitInt(1)))): int)))));
  requires _module.__default.MaybePtr#canCall(_module._default.InsertAfter$A, l#0, p#0)
     ==> _module.__default.MaybePtr(_module._default.InsertAfter$A, l#0, p#0)
       || 
      p#0 == LitInt(0)
       || _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0);
  free ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     && 
    _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
     && $Is(_module.DList.nodes(l'#0), 
      TSeq(Tclass._module.Node(_module._default.InsertAfter$A)))
     && $Is(_module.DList.s(l'#0), TSeq(_module._default.InsertAfter$A))
     && $Is(_module.DList.f(l'#0), TSeq(TInt))
     && $Is(_module.DList.g(l'#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.InsertAfter$A, 
      _module.DList.nodes(l'#0), 
      _module.DList.freeStack(l'#0), 
      _module.DList.s(l'#0), 
      _module.DList.f(l'#0), 
      _module.DList.g(l'#0));
  free ensures _module.__default.Seq#canCall(_module._default.InsertAfter$A, l'#0)
     && 
    _module.__default.Seq#canCall(_module._default.InsertAfter$A, l#0)
     && 
    _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0)
     && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1))
     && _module.__default.SeqInsert#canCall(_module._default.InsertAfter$A, 
      _module.__default.Seq(_module._default.InsertAfter$A, l#0), 
      _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)), 
      a#0);
  ensures Seq#Equal(_module.__default.Seq(_module._default.InsertAfter$A, l'#0), 
    _module.__default.SeqInsert(_module._default.InsertAfter$A, 
      _module.__default.Seq(_module._default.InsertAfter$A, l#0), 
      _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)), 
      a#0));
  free ensures _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
     && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, p'#0)
       ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
         && 
        _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0)
         && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)));
  free ensures _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
     && 
    _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, p'#0)
     && 
    0 < p'#0
     && p'#0 < Seq#Length(_module.DList.g(l'#0))
     && $Unbox(Seq#Index(_module.DList.g(l'#0), p'#0)): int >= LitInt(0);
  ensures _module.__default.Index(_module._default.InsertAfter$A, l'#0, p'#0)
     == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1));
  free ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1) } 
    _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l#0, x#1)
       && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, x#1))
       && (
        (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1))
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
             ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#1)
               && _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0)
               && (_module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
                   <= _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
                 ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, x#1)
                   && _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#1))
               && (_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
                   < _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
                 ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, x#1)
                   && 
                  _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#1)
                   && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#1), LitInt(1))))));
  ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1) } 
    true
       ==> (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1))
         && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
           ==> (if _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
               <= _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
             then _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1)
               == _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
             else _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1)
               == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#1), LitInt(1)))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.InsertAfter(_module._default.InsertAfter$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.InsertAfter$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.InsertAfter$A)
         && $IsAllocBox(a#0, _module._default.InsertAfter$A, $Heap))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.InsertAfter$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap), 
    p'#0: int, 
    $_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Inv#canCall(_module._default.InsertAfter$A, l#0)
     && 
    _module.__default.Inv(_module._default.InsertAfter$A, l#0)
     && $Is(_module.DList.nodes(l#0), 
      TSeq(Tclass._module.Node(_module._default.InsertAfter$A)))
     && $Is(_module.DList.s(l#0), TSeq(_module._default.InsertAfter$A))
     && $Is(_module.DList.f(l#0), TSeq(TInt))
     && $Is(_module.DList.g(l#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.InsertAfter$A, 
      _module.DList.nodes(l#0), 
      _module.DList.freeStack(l#0), 
      _module.DList.s(l#0), 
      _module.DList.f(l#0), 
      _module.DList.g(l#0));
  free requires _module.__default.MaybePtr#canCall(_module._default.InsertAfter$A, l#0, p#0)
     && 
    _module.__default.MaybePtr(_module._default.InsertAfter$A, l#0, p#0)
     && (p#0 == LitInt(0)
       || _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, p#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0);
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.f(l'#0)) == Seq#Length(_module.DList.s(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.g(l'#0)) == Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.nodes(l'#0)) > 0);
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || $Unbox(Seq#Index(_module.DList.g(l'#0), LitInt(0))): int
             == _module.__default.sentinel());
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || LitInt(0) <= _module.DList.freeStack(l'#0));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || _module.DList.freeStack(l'#0) < Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#6: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int
                     < Seq#Length(_module.DList.nodes(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(_module.DList.f(l'#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int
                 == i#7));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#22: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int } 
            true
               ==> (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.__default.unused()
                     <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int)
                 && (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int
                     < Seq#Length(_module.DList.s(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#23: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#23 && p#23 < Seq#Length(_module.DList.g(l'#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType))
                 && (LitInt(0) <= p#23 && p#23 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType)
                     < Seq#Length(_module.DList.g(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#24: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#24)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#24 && p#24 < Seq#Length(_module.DList.g(l'#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#24)): DatatypeType)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#25: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int } 
            true
               ==> 
              LitInt(0) <= p#25
                 && p#25 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
                 == _module.__default.sentinel()
               ==> p#25 == LitInt(0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#26: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)): int } 
              { Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int) } 
            true
               ==> 
              LitInt(0) <= p#26
                 && p#26 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)): int
                   == p#26
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#26)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#27: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#27
                 && p#27 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l'#0))
                   then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int, LitInt(1)))): int
                   else 0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertAfter$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertAfter$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertAfter$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertAfter$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#28: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#28)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#28
                     && p#28 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int
                   ==> true)
                 && (LitInt(0) <= p#28
                     && p#28 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#28)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l'#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l'#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l'#0)), LitInt(1)))): int)))));
  free ensures _module.__default.Seq#canCall(_module._default.InsertAfter$A, l'#0)
     && 
    _module.__default.Seq#canCall(_module._default.InsertAfter$A, l#0)
     && 
    _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0)
     && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1))
     && _module.__default.SeqInsert#canCall(_module._default.InsertAfter$A, 
      _module.__default.Seq(_module._default.InsertAfter$A, l#0), 
      _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)), 
      a#0);
  ensures Seq#Equal(_module.__default.Seq(_module._default.InsertAfter$A, l'#0), 
    _module.__default.SeqInsert(_module._default.InsertAfter$A, 
      _module.__default.Seq(_module._default.InsertAfter$A, l#0), 
      _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)), 
      a#0));
  free ensures _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
     && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, p'#0)
       ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
         && 
        _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0)
         && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1)));
  ensures _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
     ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, p'#0)
       || 0 < p'#0;
  ensures _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
     ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, p'#0)
       || p'#0 < Seq#Length(_module.DList.g(l'#0));
  ensures _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, p'#0)
     ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, p'#0)
       || $Unbox(Seq#Index(_module.DList.g(l'#0), p'#0)): int >= LitInt(0);
  ensures _module.__default.Index(_module._default.InsertAfter$A, l'#0, p'#0)
     == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0), LitInt(1));
  free ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1) } 
    _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l#0, x#1)
       && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l'#0, x#1))
       && (
        (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1))
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertAfter$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
             ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#1)
               && _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, p#0)
               && (_module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
                   <= _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
                 ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, x#1)
                   && _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#1))
               && (_module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
                   < _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
                 ==> _module.__default.Index#canCall(_module._default.InsertAfter$A, l'#0, x#1)
                   && 
                  _module.__default.Index#canCall(_module._default.InsertAfter$A, l#0, x#1)
                   && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#1), LitInt(1))))));
  ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1) } 
    true
       ==> (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.InsertAfter$A, l'#0, x#1))
         && (_module.__default.ValidPtr(_module._default.InsertAfter$A, l#0, x#1)
           ==> (if _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
               <= _module.__default.Index(_module._default.InsertAfter$A, l#0, p#0)
             then _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1)
               == _module.__default.Index(_module._default.InsertAfter$A, l#0, x#1)
             else _module.__default.Index(_module._default.InsertAfter$A, l'#0, x#1)
               == _module.__default.Add(_module.__default.Index(_module._default.InsertAfter$A, l#0, x#1), LitInt(1)))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.InsertAfter(_module._default.InsertAfter$A: Ty, l#0: DatatypeType, p#0: int, a#0: Box)
   returns (l'#0: DatatypeType, p'#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var freeNode#0: DatatypeType
     where $Is(freeNode#0, Tclass._module.Node(_module._default.InsertAfter$A))
       && $IsAlloc(freeNode#0, Tclass._module.Node(_module._default.InsertAfter$A), $Heap);
  var ##s#1: Seq Box;
  var ##i#0: int;
  var $rhs##0_0: DatatypeType
     where $Is($rhs##0_0, Tclass._module.DList(_module._default.InsertAfter$A))
       && $IsAlloc($rhs##0_0, Tclass._module.DList(_module._default.InsertAfter$A), $Heap);
  var l##0_0: DatatypeType;
  var ##s#0_0: Seq Box;
  var ##i#0_0: int;
  var nodes#0: Seq Box;
  var freeStack#0: int;
  var s#0: Seq Box;
  var f#0: Seq Box;
  var g#0: Seq Box;
  var let#0#0#0: DatatypeType;
  var index#0: int;
  var index'#0: int;
  var ##a#3: int;
  var ##b#3: int;
  var s'#0: Seq Box
     where $Is(s'#0, TSeq(_module._default.InsertAfter$A))
       && $IsAlloc(s'#0, TSeq(_module._default.InsertAfter$A), $Heap);
  var ##s#2: Seq Box;
  var ##k#1: int;
  var ##v#1: Box;
  var f'#0: Seq Box where $Is(f'#0, TSeq(TInt)) && $IsAlloc(f'#0, TSeq(TInt), $Heap);
  var ##s#3: Seq Box;
  var ##k#2: int;
  var ##v#2: int;
  var g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap);
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var g##0: Seq Box;
  var p'##0: int;
  var index##0: int;
  var index'##0: int;
  var node#0: DatatypeType
     where $Is(node#0, Tclass._module.Node(_module._default.InsertAfter$A))
       && $IsAlloc(node#0, Tclass._module.Node(_module._default.InsertAfter$A), $Heap);
  var ##s#4: Seq Box;
  var ##i#1: int;
  var node'#0: DatatypeType
     where $Is(node'#0, Tclass._module.Node(_module._default.InsertAfter$A))
       && $IsAlloc(node'#0, Tclass._module.Node(_module._default.InsertAfter$A), $Heap);
  var dt_update_tmp#0#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var dt_update#next#0#0: int;
  var let#2#0#0: int;
  var ##s1#0: Seq Box;
  var ##i#2: int;
  var ##a#4: DatatypeType;
  var node_next#0: DatatypeType
     where $Is(node_next#0, Tclass._module.Node(_module._default.InsertAfter$A))
       && $IsAlloc(node_next#0, Tclass._module.Node(_module._default.InsertAfter$A), $Heap);
  var ##s#5: Seq Box;
  var ##i#3: int;
  var dt_update_tmp#1#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var dt_update#prev#0#0: int;
  var let#4#0#0: int;
  var ##s1#1: Seq Box;
  var ##i#4: int;
  var ##a#5: DatatypeType;
  var ##s1#2: Seq Box;
  var ##i#5: int;
  var ##a#6: DatatypeType;

    // AddMethodImpl: InsertAfter, Impl$$_module.__default.InsertAfter
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(311,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- DLL_Dafny.dfy(312,6)
    assume true;
    assume true;
    l'#0 := l#0;
    assume {:captureState "DLL_Dafny.dfy(312,9)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(313,6)
    assume true;
    assume _module.DList.DList_q(l'#0);
    assume _module.DList.DList_q(l'#0);
    p'#0 := _module.DList.freeStack(l'#0);
    assume {:captureState "DLL_Dafny.dfy(313,20)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(314,16)
    assume true;
    assume _module.DList.DList_q(l'#0);
    ##s#1 := _module.DList.nodes(l'#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
    ##i#0 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#0;
    assert {:subsumption 0} ##i#0 < Seq#Length(##s#1);
    assume LitInt(0) <= ##i#0 && ##i#0 < Seq#Length(##s#1);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
      _module.DList.nodes(l'#0), 
      p'#0);
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), 
          _module.DList.nodes(l'#0), 
          p'#0)): DatatypeType);
    assume _module.DList.DList_q(l'#0)
       && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
        _module.DList.nodes(l'#0), 
        p'#0);
    freeNode#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), 
        _module.DList.nodes(l'#0), 
        p'#0)): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(314,39)"} true;
    // ----- if statement ----- DLL_Dafny.dfy(315,3)
    if (p'#0 != LitInt(0))
    {
        assume _module.Node.Node_q(freeNode#0);
    }

    assume p'#0 != LitInt(0) ==> _module.Node.Node_q(freeNode#0);
    if (p'#0 == LitInt(0) || _module.Option.Some_q(_module.Node.data(freeNode#0)))
    {
        // ----- call statement ----- DLL_Dafny.dfy(316,17)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<A>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        l##0_0 := l'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.__default.Expand(_module._default.InsertAfter$A, l##0_0);
        // TrCallStmt: After ProcessCallStmt
        l'#0 := $rhs##0_0;
        assume {:captureState "DLL_Dafny.dfy(316,20)"} true;
        // ----- assignment statement ----- DLL_Dafny.dfy(317,8)
        assume true;
        assume _module.DList.DList_q(l'#0);
        assume _module.DList.DList_q(l'#0);
        p'#0 := _module.DList.freeStack(l'#0);
        assume {:captureState "DLL_Dafny.dfy(317,22)"} true;
        // ----- assignment statement ----- DLL_Dafny.dfy(318,14)
        assume true;
        assume _module.DList.DList_q(l'#0);
        ##s#0_0 := _module.DList.nodes(l'#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
        ##i#0_0 := p'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#0_0, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#0_0;
        assert {:subsumption 0} ##i#0_0 < Seq#Length(##s#0_0);
        assume LitInt(0) <= ##i#0_0 && ##i#0_0 < Seq#Length(##s#0_0);
        assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
          _module.DList.nodes(l'#0), 
          p'#0);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), 
              _module.DList.nodes(l'#0), 
              p'#0)): DatatypeType);
        assume _module.DList.DList_q(l'#0)
           && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
            _module.DList.nodes(l'#0), 
            p'#0);
        freeNode#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), 
            _module.DList.nodes(l'#0), 
            p'#0)): DatatypeType;
        assume {:captureState "DLL_Dafny.dfy(318,37)"} true;
    }
    else
    {
    }

    havoc nodes#0;
    assume $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)))
       && $IsAlloc(nodes#0, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
    havoc freeStack#0;
    havoc s#0;
    assume $Is(s#0, TSeq(_module._default.InsertAfter$A))
       && $IsAlloc(s#0, TSeq(_module._default.InsertAfter$A), $Heap);
    havoc f#0;
    assume $Is(f#0, TSeq(TInt)) && $IsAlloc(f#0, TSeq(TInt), $Heap);
    havoc g#0;
    assume $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap);
    assume let#0#0#0 == l'#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.DList(_module._default.InsertAfter$A));
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume #_module.DList.DList(nodes#0, freeStack#0, s#0, f#0, g#0) == let#0#0#0;
    // ----- assignment statement ----- DLL_Dafny.dfy(321,19)
    assume true;
    assert 0 <= p#0 && p#0 < Seq#Length(g#0);
    assume true;
    index#0 := $Unbox(Seq#Index(g#0, p#0)): int;
    assume {:captureState "DLL_Dafny.dfy(321,25)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(322,20)
    assume true;
    ##a#3 := index#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, TInt, $Heap);
    ##b#3 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, TInt, $Heap);
    assume _module.__default.Add#canCall(index#0, LitInt(1));
    assume _module.__default.Add#canCall(index#0, LitInt(1));
    index'#0 := _module.__default.Add(index#0, LitInt(1));
    assume {:captureState "DLL_Dafny.dfy(322,35)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(323,16)
    assume true;
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, TSeq(_module._default.InsertAfter$A), $Heap);
    ##k#1 := index'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#1, TInt, $Heap);
    ##v#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##v#1, _module._default.InsertAfter$A, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#1;
    assert {:subsumption 0} ##k#1 <= Seq#Length(##s#2);
    assume LitInt(0) <= ##k#1 && ##k#1 <= Seq#Length(##s#2);
    assume _module.__default.SeqInsert#canCall(_module._default.InsertAfter$A, s#0, index'#0, a#0);
    assume _module.__default.SeqInsert#canCall(_module._default.InsertAfter$A, s#0, index'#0, a#0);
    s'#0 := _module.__default.SeqInsert(_module._default.InsertAfter$A, s#0, index'#0, a#0);
    assume {:captureState "DLL_Dafny.dfy(323,41)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(324,16)
    assume true;
    ##s#3 := f#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, TSeq(TInt), $Heap);
    ##k#2 := index'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#2, TInt, $Heap);
    ##v#2 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##v#2, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#2;
    assert {:subsumption 0} ##k#2 <= Seq#Length(##s#3);
    assume LitInt(0) <= ##k#2 && ##k#2 <= Seq#Length(##s#3);
    assume _module.__default.SeqInsert#canCall(TInt, f#0, index'#0, $Box(p'#0));
    assume _module.__default.SeqInsert#canCall(TInt, f#0, index'#0, $Box(p'#0));
    f'#0 := _module.__default.SeqInsert(TInt, f#0, index'#0, $Box(p'#0));
    assume {:captureState "DLL_Dafny.dfy(324,42)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(325,38)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type seq<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    g##0 := g#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p'##0 := p'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    index##0 := index#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    index'##0 := index'#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.InsertAfter__SeqInit(g##0, p'##0, index##0, index'##0);
    // TrCallStmt: After ProcessCallStmt
    g'#0 := $rhs##0;
    assume {:captureState "DLL_Dafny.dfy(325,59)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(326,12)
    assume true;
    ##s#4 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#4, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
    ##i#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#1;
    assert {:subsumption 0} ##i#1 < Seq#Length(##s#4);
    assume LitInt(0) <= ##i#1 && ##i#1 < Seq#Length(##s#4);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), nodes#0, p#0);
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), nodes#0, p#0)): DatatypeType);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), nodes#0, p#0);
    node#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), nodes#0, p#0)): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(326,31)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(327,13)
    assume true;
    assume _module.Node.Node_q(node#0);
    assume _module.Node.Node_q(node#0);
    node'#0 := #_module.Node.Node(#_module.Option.Some(a#0), _module.Node.next(node#0), p#0);
    assume {:captureState "DLL_Dafny.dfy(327,42)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(328,9)
    assume true;
    havoc dt_update_tmp#0#0;
    assume $Is(dt_update_tmp#0#0, Tclass._module.Node(_module._default.InsertAfter$A));
    assume let#1#0#0 == node#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, Tclass._module.Node(_module._default.InsertAfter$A));
    assume dt_update_tmp#0#0 == let#1#0#0;
    havoc dt_update#next#0#0;
    assume let#2#0#0 == p'#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#2#0#0, TInt);
    assume dt_update#next#0#0 == let#2#0#0;
    assume _module.Node.Node_q(dt_update_tmp#0#0);
    assume _module.Node.Node_q(dt_update_tmp#0#0);
    ##s1#0 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#0, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
    ##i#2 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#2, TInt, $Heap);
    ##a#4 := (var dt_update_tmp#0#1 := node#0; 
      (var dt_update#next#0#1 := p'#0; 
        #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
          dt_update#next#0#1, 
          _module.Node.prev(dt_update_tmp#0#1))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#4, Tclass._module.Node(_module._default.InsertAfter$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#2;
    assert {:subsumption 0} ##i#2 < Seq#Length(##s1#0);
    assume LitInt(0) <= ##i#2 && ##i#2 < Seq#Length(##s1#0);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      p#0, 
      $Box((var dt_update_tmp#0#1 := node#0; 
          (var dt_update#next#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
              dt_update#next#0#1, 
              _module.Node.prev(dt_update_tmp#0#1))))));
    assume (var dt_update_tmp#0#1 := node#0; 
        _module.Node.Node_q(dt_update_tmp#0#1) && _module.Node.Node_q(dt_update_tmp#0#1))
       && _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
        nodes#0, 
        p#0, 
        $Box((var dt_update_tmp#0#1 := node#0; 
            (var dt_update#next#0#1 := p'#0; 
              #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
                dt_update#next#0#1, 
                _module.Node.prev(dt_update_tmp#0#1))))));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      p#0, 
      $Box((var dt_update_tmp#0#1 := node#0; 
          (var dt_update#next#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
              dt_update#next#0#1, 
              _module.Node.prev(dt_update_tmp#0#1))))));
    assume {:captureState "DLL_Dafny.dfy(328,47)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(329,17)
    assume true;
    assume _module.Node.Node_q(node#0);
    ##s#5 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#5, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
    ##i#3 := _module.Node.next(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#3;
    assert {:subsumption 0} ##i#3 < Seq#Length(##s#5);
    assume LitInt(0) <= ##i#3 && ##i#3 < Seq#Length(##s#5);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      _module.Node.next(node#0));
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), 
          nodes#0, 
          _module.Node.next(node#0))): DatatypeType);
    assume _module.Node.Node_q(node#0)
       && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
        nodes#0, 
        _module.Node.next(node#0));
    node_next#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertAfter$A), 
        nodes#0, 
        _module.Node.next(node#0))): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(329,44)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(330,9)
    assume true;
    assume _module.Node.Node_q(node#0);
    havoc dt_update_tmp#1#0;
    assume $Is(dt_update_tmp#1#0, Tclass._module.Node(_module._default.InsertAfter$A));
    assume let#3#0#0 == node_next#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#3#0#0, Tclass._module.Node(_module._default.InsertAfter$A));
    assume dt_update_tmp#1#0 == let#3#0#0;
    havoc dt_update#prev#0#0;
    assume let#4#0#0 == p'#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#4#0#0, TInt);
    assume dt_update#prev#0#0 == let#4#0#0;
    assume _module.Node.Node_q(dt_update_tmp#1#0);
    assume _module.Node.Node_q(dt_update_tmp#1#0);
    ##s1#1 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#1, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
    ##i#4 := _module.Node.next(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#4, TInt, $Heap);
    ##a#5 := (var dt_update_tmp#1#1 := node_next#0; 
      (var dt_update#prev#0#1 := p'#0; 
        #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
          _module.Node.next(dt_update_tmp#1#1), 
          dt_update#prev#0#1)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#5, Tclass._module.Node(_module._default.InsertAfter$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#4;
    assert {:subsumption 0} ##i#4 < Seq#Length(##s1#1);
    assume LitInt(0) <= ##i#4 && ##i#4 < Seq#Length(##s1#1);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      _module.Node.next(node#0), 
      $Box((var dt_update_tmp#1#1 := node_next#0; 
          (var dt_update#prev#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
              _module.Node.next(dt_update_tmp#1#1), 
              dt_update#prev#0#1)))));
    assume _module.Node.Node_q(node#0)
       && (var dt_update_tmp#1#1 := node_next#0; 
        _module.Node.Node_q(dt_update_tmp#1#1) && _module.Node.Node_q(dt_update_tmp#1#1))
       && _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
        nodes#0, 
        _module.Node.next(node#0), 
        $Box((var dt_update_tmp#1#1 := node_next#0; 
            (var dt_update#prev#0#1 := p'#0; 
              #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
                _module.Node.next(dt_update_tmp#1#1), 
                dt_update#prev#0#1)))));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      _module.Node.next(node#0), 
      $Box((var dt_update_tmp#1#1 := node_next#0; 
          (var dt_update#prev#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
              _module.Node.next(dt_update_tmp#1#1), 
              dt_update#prev#0#1)))));
    assume {:captureState "DLL_Dafny.dfy(330,60)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(331,9)
    assume true;
    ##s1#2 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#2, TSeq(Tclass._module.Node(_module._default.InsertAfter$A)), $Heap);
    ##i#5 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#5, TInt, $Heap);
    ##a#6 := node'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#6, Tclass._module.Node(_module._default.InsertAfter$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#5;
    assert {:subsumption 0} ##i#5 < Seq#Length(##s1#2);
    assume LitInt(0) <= ##i#5 && ##i#5 < Seq#Length(##s1#2);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      p'#0, 
      $Box(node'#0));
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      p'#0, 
      $Box(node'#0));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.InsertAfter$A), 
      nodes#0, 
      p'#0, 
      $Box(node'#0));
    assume {:captureState "DLL_Dafny.dfy(331,36)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(332,6)
    assume true;
    assume _module.Node.Node_q(freeNode#0);
    assume _module.Node.Node_q(freeNode#0);
    l'#0 := #_module.DList.DList(nodes#0, _module.Node.next(freeNode#0), s'#0, f'#0, g'#0);
    assume {:captureState "DLL_Dafny.dfy(332,47)"} true;
}



procedure CheckWellformed$$_module.__default.InsertBefore__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    p'#0: int, 
    index'#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InsertBefore__SeqInit(g#0: Seq Box, p'#0: int, index'#0: int) returns (g'#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: InsertBefore_SeqInit, CheckWellformed$$_module.__default.InsertBefore__SeqInit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(338,13): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc g'#0;
    assume {:captureState "DLL_Dafny.dfy(339,15): post-state"} true;
    assume Seq#Length(g'#0) == Seq#Length(g#0);
    havoc x#0;
    if (*)
    {
        assume LitInt(0) <= x#0;
        assume x#0 < Seq#Length(g#0);
        if (*)
        {
            assume x#0 == p'#0;
            assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
            assume $Unbox(Seq#Index(g'#0, x#0)): int == index'#0;
        }
        else
        {
            assume x#0 != p'#0;
            if (*)
            {
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                assume index'#0 <= $Unbox(Seq#Index(g#0, x#0)): int;
                assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                ##a#0 := $Unbox(Seq#Index(g#0, x#0)): int;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, TInt, $Heap);
                ##b#0 := LitInt(1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, TInt, $Heap);
                assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1));
                assume $Unbox(Seq#Index(g'#0, x#0)): int
                   == _module.__default.Add($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1));
            }
            else
            {
                assume $Unbox(Seq#Index(g#0, x#0)): int < index'#0;
                assert 0 <= x#0 && x#0 < Seq#Length(g'#0);
                assert 0 <= x#0 && x#0 < Seq#Length(g#0);
                assume $Unbox(Seq#Index(g'#0, x#0)): int == $Unbox(Seq#Index(g#0, x#0)): int;
            }
        }
    }
    else
    {
        assume LitInt(0) <= x#0 && x#0 < Seq#Length(g#0)
           ==> (if x#0 == p'#0
             then $Unbox(Seq#Index(g'#0, x#0)): int == index'#0
             else (if index'#0 <= $Unbox(Seq#Index(g#0, x#0)): int
               then $Unbox(Seq#Index(g'#0, x#0)): int
                 == _module.__default.Add($Unbox(Seq#Index(g#0, x#0)): int, LitInt(1))
               else $Unbox(Seq#Index(g'#0, x#0)): int == $Unbox(Seq#Index(g#0, x#0)): int));
    }

    assume (forall x#1: int :: 
      { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
      true
         ==> 
        LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
         ==> (if x#1 == p'#0
           then $Unbox(Seq#Index(g'#0, x#1)): int == index'#0
           else (if index'#0 <= $Unbox(Seq#Index(g#0, x#1)): int
             then $Unbox(Seq#Index(g'#0, x#1)): int
               == _module.__default.Add($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
             else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
}



procedure Call$$_module.__default.InsertBefore__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    p'#0: int, 
    index'#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(g'#0) == Seq#Length(g#0);
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> 
      x#1 != p'#0
       ==> 
      index'#0 <= $Unbox(Seq#Index(g#0, x#1)): int
       ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1)));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    true
       ==> 
      LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> (if x#1 == p'#0
         then $Unbox(Seq#Index(g'#0, x#1)): int == index'#0
         else (if index'#0 <= $Unbox(Seq#Index(g#0, x#1)): int
           then $Unbox(Seq#Index(g'#0, x#1)): int
             == _module.__default.Add($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
           else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.InsertBefore__SeqInit(g#0: Seq Box where $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap), 
    p'#0: int, 
    index'#0: int)
   returns (g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(g'#0) == Seq#Length(g#0);
  free ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> 
      x#1 != p'#0
       ==> 
      index'#0 <= $Unbox(Seq#Index(g#0, x#1)): int
       ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1)));
  ensures (forall x#1: int :: 
    { $Unbox(Seq#Index(g'#0, x#1)): int } { $Unbox(Seq#Index(g#0, x#1)): int } 
    true
       ==> 
      LitInt(0) <= x#1 && x#1 < Seq#Length(g#0)
       ==> (if x#1 == p'#0
         then $Unbox(Seq#Index(g'#0, x#1)): int == index'#0
         else (if index'#0 <= $Unbox(Seq#Index(g#0, x#1)): int
           then $Unbox(Seq#Index(g'#0, x#1)): int
             == _module.__default.Add($Unbox(Seq#Index(g#0, x#1)): int, LitInt(1))
           else $Unbox(Seq#Index(g'#0, x#1)): int == $Unbox(Seq#Index(g#0, x#1)): int)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.InsertBefore__SeqInit(g#0: Seq Box, p'#0: int, index'#0: int)
   returns (g'#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: int;
  var ##a#1: int;
  var ##b#1: int;
  var ##len#0: int;
  var ##func#0: HandleType;

    // AddMethodImpl: InsertBefore_SeqInit, Impl$$_module.__default.InsertBefore__SeqInit
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(345,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- DLL_Dafny.dfy(346,8)
    assume true;
    havoc x#2;
    // Begin Comprehension WF check
    if (*)
    {
        $oldHeap#0 := $Heap;
        havoc $Heap;
        assume $IsGoodHeap($Heap);
        assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
        $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (LitInt(0) <= x#2)
        {
        }

        if (LitInt(0) <= x#2 && x#2 < Seq#Length(g#0))
        {
            if (x#2 == p'#0)
            {
                assume lambdaResult#0 == index'#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, TInt);
            }
            else
            {
                assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                if ($Unbox(Seq#Index(g#0, x#2)): int >= index'#0)
                {
                    assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                    ##a#1 := $Unbox(Seq#Index(g#0, x#2)): int;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##a#1, TInt, $Heap);
                    ##b#1 := LitInt(1);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##b#1, TInt, $Heap);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame#l0[$o, $f]);
                    assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    assume lambdaResult#0
                       == _module.__default.Add($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    assume _module.__default.Add#canCall($Unbox(Seq#Index(g#0, x#2)): int, LitInt(1));
                    // CheckWellformedWithResult: any expression
                    assume $Is(lambdaResult#0, TInt);
                }
                else
                {
                    assert 0 <= x#2 && x#2 < Seq#Length(g#0);
                    assume lambdaResult#0 == $Unbox(Seq#Index(g#0, x#2)): int;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(lambdaResult#0, TInt);
                }
            }
        }

        assume false;
    }

    // End Comprehension WF check
    ##len#0 := Seq#Length(g#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##len#0, TInt, $Heap);
    ##func#0 := Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
          Handle1((lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              $Box((if $Unbox($l#1#x#0): int == p'#0
                   then index'#0
                   else (if $Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int >= index'#0
                     then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int, LitInt(1))
                     else $Unbox(Seq#Index(g#0, $Unbox($l#1#x#0): int)): int)))), 
            (lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              $IsBox($l#1#x#0, TInt)
                 && 
                LitInt(0) <= $Unbox($l#1#x#0): int
                 && $Unbox($l#1#x#0): int < Seq#Length(g#0)), 
            (lambda $l#1#heap#0: Heap, $l#1#x#0: Box :: 
              SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
        $LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##func#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap);
    assert {:subsumption 0} ##len#0 >= LitInt(0);
    assume ##len#0 >= LitInt(0);
    assert {:subsumption 0} (forall i#0: int :: 
      { Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)) } 
      true
         ==> 
        LitInt(0) <= i#0 && i#0 < ##len#0
         ==> Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)));
    assume (forall i#0: int :: 
      { Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)) } 
      true
         ==> 
        LitInt(0) <= i#0 && i#0 < ##len#0
         ==> Requires1(TInt, TInt, $Heap, ##func#0, $Box(i#0)));
    assume _module.__default.SeqInit#canCall(TInt, 
      Seq#Length(g#0), 
      Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
            Handle1((lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                $Box((if $Unbox($l#2#x#0): int == p'#0
                     then index'#0
                     else (if $Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int >= index'#0
                       then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int, LitInt(1))
                       else $Unbox(Seq#Index(g#0, $Unbox($l#2#x#0): int)): int)))), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                $IsBox($l#2#x#0, TInt)
                   && 
                  LitInt(0) <= $Unbox($l#2#x#0): int
                   && $Unbox($l#2#x#0): int < Seq#Length(g#0)), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
          $LS($LZ))));
    assume (forall $l#3#x#0: int :: 
        LitInt(0) <= $l#3#x#0 && $l#3#x#0 < Seq#Length(g#0)
           ==> 
          $l#3#x#0 != p'#0
           ==> 
          $Unbox(Seq#Index(g#0, $l#3#x#0)): int >= index'#0
           ==> _module.__default.Add#canCall($Unbox(Seq#Index(g#0, $l#3#x#0)): int, LitInt(1)))
       && _module.__default.SeqInit#canCall(TInt, 
        Seq#Length(g#0), 
        Lit(AtLayer((lambda $l#4#ly#0: LayerType :: 
              Handle1((lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  $Box((if $Unbox($l#4#x#0): int == p'#0
                       then index'#0
                       else (if $Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int >= index'#0
                         then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int, LitInt(1))
                         else $Unbox(Seq#Index(g#0, $Unbox($l#4#x#0): int)): int)))), 
                (lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  $IsBox($l#4#x#0, TInt)
                     && 
                    LitInt(0) <= $Unbox($l#4#x#0): int
                     && $Unbox($l#4#x#0): int < Seq#Length(g#0)), 
                (lambda $l#4#heap#0: Heap, $l#4#x#0: Box :: 
                  SetRef_to_SetBox((lambda $l#4#o#0: ref :: false))))), 
            $LS($LZ))));
    g'#0 := _module.__default.SeqInit(TInt, 
      Seq#Length(g#0), 
      Lit(AtLayer((lambda $l#5#ly#0: LayerType :: 
            Handle1((lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                $Box((if $Unbox($l#5#x#0): int == p'#0
                     then index'#0
                     else (if $Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int >= index'#0
                       then _module.__default.Add($Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int, LitInt(1))
                       else $Unbox(Seq#Index(g#0, $Unbox($l#5#x#0): int)): int)))), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                $IsBox($l#5#x#0, TInt)
                   && 
                  LitInt(0) <= $Unbox($l#5#x#0): int
                   && $Unbox($l#5#x#0): int < Seq#Length(g#0)), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#5#o#0: ref :: false))))), 
          $LS($LZ))));
    assume {:captureState "DLL_Dafny.dfy(347,78)"} true;
}



procedure CheckWellformed$$_module.__default.InsertBefore(_module._default.InsertBefore$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.InsertBefore$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.InsertBefore$A)
         && $IsAllocBox(a#0, _module._default.InsertBefore$A, $Heap))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.InsertBefore$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap), 
    p'#0: int);
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InsertBefore(_module._default.InsertBefore$A: Ty, l#0: DatatypeType, p#0: int, a#0: Box)
   returns (l'#0: DatatypeType, p'#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var ##l#1: DatatypeType;
  var ##p#0: int;
  var ##l#2: DatatypeType;
  var ##l#3: DatatypeType;
  var ##l#4: DatatypeType;
  var ##l#5: DatatypeType;
  var ##p#1: int;
  var ##s#0: Seq Box;
  var ##k#0: int;
  var ##v#0: Box;
  var ##l#6: DatatypeType;
  var ##p#2: int;
  var ##l#7: DatatypeType;
  var ##p#3: int;
  var ##l#8: DatatypeType;
  var ##p#4: int;
  var x#0: int;
  var ##l#9: DatatypeType;
  var ##p#5: int;
  var ##l#10: DatatypeType;
  var ##p#6: int;
  var ##l#11: DatatypeType;
  var ##p#7: int;
  var ##l#12: DatatypeType;
  var ##p#8: int;
  var ##l#13: DatatypeType;
  var ##p#9: int;
  var ##l#14: DatatypeType;
  var ##p#10: int;
  var ##l#15: DatatypeType;
  var ##p#11: int;
  var ##l#16: DatatypeType;
  var ##p#12: int;
  var ##a#0: int;
  var ##b#0: int;

    // AddMethodImpl: InsertBefore, CheckWellformed$$_module.__default.InsertBefore
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(351,7): initial state"} true;
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0);
    assume _module.__default.Inv(_module._default.InsertBefore$A, l#0);
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    ##p#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#0, TInt, $Heap);
    assume _module.__default.MaybePtr#canCall(_module._default.InsertBefore$A, l#0, p#0);
    assume _module.__default.MaybePtr(_module._default.InsertBefore$A, l#0, p#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc l'#0, p'#0;
    assume {:captureState "DLL_Dafny.dfy(354,13): post-state"} true;
    ##l#2 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#2, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    assume _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0);
    assume _module.__default.Inv(_module._default.InsertBefore$A, l'#0);
    ##l#3 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#3, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    assume _module.__default.Seq#canCall(_module._default.InsertBefore$A, l'#0);
    ##l#4 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#4, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    assume _module.__default.Seq#canCall(_module._default.InsertBefore$A, l#0);
    ##l#5 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#5, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    ##p#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#1, TInt, $Heap);
    assume _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0);
    ##s#0 := _module.__default.Seq(_module._default.InsertBefore$A, l#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(_module._default.InsertBefore$A), $Heap);
    ##k#0 := _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#0, TInt, $Heap);
    ##v#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##v#0, _module._default.InsertBefore$A, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#0;
    assert {:subsumption 0} ##k#0 <= Seq#Length(##s#0);
    assume LitInt(0) <= ##k#0 && ##k#0 <= Seq#Length(##s#0);
    assume _module.__default.SeqInsert#canCall(_module._default.InsertBefore$A, 
      _module.__default.Seq(_module._default.InsertBefore$A, l#0), 
      _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0), 
      a#0);
    assume Seq#Equal(_module.__default.Seq(_module._default.InsertBefore$A, l'#0), 
      _module.__default.SeqInsert(_module._default.InsertBefore$A, 
        _module.__default.Seq(_module._default.InsertBefore$A, l#0), 
        _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0), 
        a#0));
    ##l#6 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#6, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    ##p#2 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#2, TInt, $Heap);
    assume _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, p'#0);
    assume _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, p'#0);
    ##l#7 := l'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#7, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    ##p#3 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#3, TInt, $Heap);
    assume _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, p'#0);
    ##l#8 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#8, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    ##p#4 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#4, TInt, $Heap);
    assume _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0);
    assume _module.__default.Index(_module._default.InsertBefore$A, l'#0, p'#0)
       == _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0);
    havoc x#0;
    if (*)
    {
        ##l#9 := l#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#9, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
        ##p#5 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#5, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l#0, x#0);
        assume _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#0);
        ##l#10 := l'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##l#10, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
        ##p#6 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#6, TInt, $Heap);
        assume _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, x#0);
        assume _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#0);
        if (*)
        {
            ##l#11 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#11, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
            ##p#7 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#7, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#0);
            ##l#12 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#12, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
            ##p#8 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#8, TInt, $Heap);
            assume _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0);
            assume _module.__default.Index(_module._default.InsertBefore$A, l#0, x#0)
               < _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0);
            ##l#13 := l'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#13, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
            ##p#9 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#9, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, x#0);
            ##l#14 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#14, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
            ##p#10 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#10, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#0);
            assume _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#0)
               == _module.__default.Index(_module._default.InsertBefore$A, l#0, x#0);
        }
        else
        {
            assume _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
               <= _module.__default.Index(_module._default.InsertBefore$A, l#0, x#0);
            ##l#15 := l'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#15, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
            ##p#11 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#11, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, x#0);
            ##l#16 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#16, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
            ##p#12 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#12, TInt, $Heap);
            assume _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#0);
            ##a#0 := _module.__default.Index(_module._default.InsertBefore$A, l#0, x#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, TInt, $Heap);
            ##b#0 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assume _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#0), LitInt(1));
            assume _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#0)
               == _module.__default.Add(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#0), LitInt(1));
        }
    }
    else
    {
        assume _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#0)
           ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#0)
             && (if _module.__default.Index(_module._default.InsertBefore$A, l#0, x#0)
                 < _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
               then _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#0)
                 == _module.__default.Index(_module._default.InsertBefore$A, l#0, x#0)
               else _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#0)
                 == _module.__default.Add(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#0), LitInt(1)));
    }

    assume (forall x#1: int :: 
      { _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1) } 
        { _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1) } 
        { _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1) } 
        { _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1) } 
      true
         ==> (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
             ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1))
           && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
             ==> (if _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
                 < _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
               then _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1)
                 == _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
               else _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1)
                 == _module.__default.Add(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#1), LitInt(1)))));
}



procedure Call$$_module.__default.InsertBefore(_module._default.InsertBefore$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.InsertBefore$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.InsertBefore$A)
         && $IsAllocBox(a#0, _module._default.InsertBefore$A, $Heap))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.InsertBefore$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap), 
    p'#0: int);
  // user-defined preconditions
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.f(l#0)) == Seq#Length(_module.DList.s(l#0)));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.g(l#0)) == Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || Seq#Length(_module.DList.nodes(l#0)) > 0);
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || $Unbox(Seq#Index(_module.DList.g(l#0), LitInt(0))): int
             == _module.__default.sentinel());
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || LitInt(0) <= _module.DList.freeStack(l#0));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || _module.DList.freeStack(l#0) < Seq#Length(_module.DList.nodes(l#0)));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#0: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int } 
            true
               ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int)
                 && (LitInt(0) <= i#0 && i#0 < Seq#Length(_module.DList.f(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l#0), i#0)): int
                     < Seq#Length(_module.DList.nodes(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall i#1: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#1 && i#1 < Seq#Length(_module.DList.f(l#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l#0), $Unbox(Seq#Index(_module.DList.f(l#0), i#1)): int)): int
                 == i#1));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#1: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int } 
            true
               ==> (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.__default.unused() <= $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int)
                 && (LitInt(0) <= p#1 && p#1 < Seq#Length(_module.DList.g(l#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l#0), p#1)): int
                     < Seq#Length(_module.DList.s(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#2: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#2 && p#2 < Seq#Length(_module.DList.g(l#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType))
                 && (LitInt(0) <= p#2 && p#2 < Seq#Length(_module.DList.g(l#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#2)): DatatypeType)
                     < Seq#Length(_module.DList.g(l#0)))));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#3: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l#0), p#3)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#3 && p#3 < Seq#Length(_module.DList.g(l#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l#0), p#3)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#3)): DatatypeType)))));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#4: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int } 
            true
               ==> 
              LitInt(0) <= p#4
                 && p#4 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l#0), p#4)): int
                 == _module.__default.sentinel()
               ==> p#4 == LitInt(0)));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#5: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)): int } 
              { Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int) } 
            true
               ==> 
              LitInt(0) <= p#5
                 && p#5 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)): int
                   == p#5
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l#0), p#5)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l#0), $Unbox(Seq#Index(_module.DList.g(l#0), p#5)): int)))));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#6: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#6
                 && p#6 < Seq#Length(_module.DList.g(l#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l#0), p#6)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l#0))
                   then $Unbox(Seq#Index(_module.DList.f(l#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l#0), p#6)): int, LitInt(1)))): int
                   else 0)));
  requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l#0), 
          _module.DList.freeStack(l#0), 
          _module.DList.s(l#0), 
          _module.DList.f(l#0), 
          _module.DList.g(l#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l#0), 
            _module.DList.freeStack(l#0), 
            _module.DList.s(l#0), 
            _module.DList.f(l#0), 
            _module.DList.g(l#0))
           || (forall p#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#7)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#7
                     && p#7 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int
                   ==> true)
                 && (LitInt(0) <= p#7
                     && p#7 < Seq#Length(_module.DList.g(l#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l#0), p#7)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l#0), p#7)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l#0)), LitInt(1)))): int)))));
  requires _module.__default.MaybePtr#canCall(_module._default.InsertBefore$A, l#0, p#0)
     ==> _module.__default.MaybePtr(_module._default.InsertBefore$A, l#0, p#0)
       || 
      p#0 == LitInt(0)
       || _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0);
  free ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     && 
    _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
     && $Is(_module.DList.nodes(l'#0), 
      TSeq(Tclass._module.Node(_module._default.InsertBefore$A)))
     && $Is(_module.DList.s(l'#0), TSeq(_module._default.InsertBefore$A))
     && $Is(_module.DList.f(l'#0), TSeq(TInt))
     && $Is(_module.DList.g(l'#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.InsertBefore$A, 
      _module.DList.nodes(l'#0), 
      _module.DList.freeStack(l'#0), 
      _module.DList.s(l'#0), 
      _module.DList.f(l'#0), 
      _module.DList.g(l'#0));
  free ensures _module.__default.Seq#canCall(_module._default.InsertBefore$A, l'#0)
     && 
    _module.__default.Seq#canCall(_module._default.InsertBefore$A, l#0)
     && _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0)
     && _module.__default.SeqInsert#canCall(_module._default.InsertBefore$A, 
      _module.__default.Seq(_module._default.InsertBefore$A, l#0), 
      _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0), 
      a#0);
  ensures Seq#Equal(_module.__default.Seq(_module._default.InsertBefore$A, l'#0), 
    _module.__default.SeqInsert(_module._default.InsertBefore$A, 
      _module.__default.Seq(_module._default.InsertBefore$A, l#0), 
      _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0), 
      a#0));
  free ensures _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
     && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, p'#0)
       ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
         && _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0));
  free ensures _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
     && 
    _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, p'#0)
     && 
    0 < p'#0
     && p'#0 < Seq#Length(_module.DList.g(l'#0))
     && $Unbox(Seq#Index(_module.DList.g(l'#0), p'#0)): int >= LitInt(0);
  ensures _module.__default.Index(_module._default.InsertBefore$A, l'#0, p'#0)
     == _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0);
  free ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1) } 
    _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l#0, x#1)
       && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, x#1))
       && (
        (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1))
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
             ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#1)
               && _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0)
               && (_module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
                   < _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
                 ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, x#1)
                   && _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#1))
               && (_module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
                   <= _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
                 ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, x#1)
                   && 
                  _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#1)
                   && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#1), LitInt(1))))));
  ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1) } 
    true
       ==> (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1))
         && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
           ==> (if _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
               < _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
             then _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1)
               == _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
             else _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1)
               == _module.__default.Add(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#1), LitInt(1)))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.InsertBefore(_module._default.InsertBefore$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.InsertBefore$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap)
         && $IsA#_module.DList(l#0), 
    p#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.InsertBefore$A)
         && $IsAllocBox(a#0, _module._default.InsertBefore$A, $Heap))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.InsertBefore$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap), 
    p'#0: int, 
    $_reverifyPost: bool);
  free requires 40 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Inv#canCall(_module._default.InsertBefore$A, l#0)
     && 
    _module.__default.Inv(_module._default.InsertBefore$A, l#0)
     && $Is(_module.DList.nodes(l#0), 
      TSeq(Tclass._module.Node(_module._default.InsertBefore$A)))
     && $Is(_module.DList.s(l#0), TSeq(_module._default.InsertBefore$A))
     && $Is(_module.DList.f(l#0), TSeq(TInt))
     && $Is(_module.DList.g(l#0), TSeq(TInt))
     && _module.__default.Invs(_module._default.InsertBefore$A, 
      _module.DList.nodes(l#0), 
      _module.DList.freeStack(l#0), 
      _module.DList.s(l#0), 
      _module.DList.f(l#0), 
      _module.DList.g(l#0));
  free requires _module.__default.MaybePtr#canCall(_module._default.InsertBefore$A, l#0, p#0)
     && 
    _module.__default.MaybePtr(_module._default.InsertBefore$A, l#0, p#0)
     && (p#0 == LitInt(0)
       || _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, p#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0);
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.f(l'#0)) == Seq#Length(_module.DList.s(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.g(l'#0)) == Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || Seq#Length(_module.DList.nodes(l'#0)) > 0);
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || $Unbox(Seq#Index(_module.DList.g(l'#0), LitInt(0))): int
             == _module.__default.sentinel());
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || LitInt(0) <= _module.DList.freeStack(l'#0));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || _module.DList.freeStack(l'#0) < Seq#Length(_module.DList.nodes(l'#0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#6: int :: 
            { $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int } 
            true
               ==> (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> 0 < $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int)
                 && (LitInt(0) <= i#6 && i#6 < Seq#Length(_module.DList.f(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.f(l'#0), i#6)): int
                     < Seq#Length(_module.DList.nodes(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall i#7: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int } 
            true
               ==> 
              LitInt(0) <= i#7 && i#7 < Seq#Length(_module.DList.f(l'#0))
               ==> $Unbox(Seq#Index(_module.DList.g(l'#0), $Unbox(Seq#Index(_module.DList.f(l'#0), i#7)): int)): int
                 == i#7));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#22: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int } 
            true
               ==> (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.__default.unused()
                     <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int)
                 && (LitInt(0) <= p#22 && p#22 < Seq#Length(_module.DList.g(l'#0))
                   ==> $Unbox(Seq#Index(_module.DList.g(l'#0), p#22)): int
                     < Seq#Length(_module.DList.s(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#23: int :: 
            { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType } 
            true
               ==> (LitInt(0) <= p#23 && p#23 < Seq#Length(_module.DList.g(l'#0))
                   ==> LitInt(0)
                     <= _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType))
                 && (LitInt(0) <= p#23 && p#23 < Seq#Length(_module.DList.g(l'#0))
                   ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#23)): DatatypeType)
                     < Seq#Length(_module.DList.g(l'#0)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#24: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int } 
              { $Unbox(Seq#Index(_module.DList.nodes(l'#0), p#24)): DatatypeType } 
            true
               ==> 
              LitInt(0) <= p#24 && p#24 < Seq#Length(_module.DList.g(l'#0))
               ==> ($Unbox(Seq#Index(_module.DList.g(l'#0), p#24)): int >= LitInt(0)
                 <==> _module.Option.Some_q(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#24)): DatatypeType)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#25: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int } 
            true
               ==> 
              LitInt(0) <= p#25
                 && p#25 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
               ==> 
              $Unbox(Seq#Index(_module.DList.g(l'#0), p#25)): int
                 == _module.__default.sentinel()
               ==> p#25 == LitInt(0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#26: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int } 
              { $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)): int } 
              { Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int) } 
            true
               ==> 
              LitInt(0) <= p#26
                 && p#26 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int
               ==> 
              LitInt(0) <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int
               ==> $Unbox(Seq#Index(_module.DList.f(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)): int
                   == p#26
                 && _module.Option#Equal(_module.Node.data($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#26)): DatatypeType), 
                  #_module.Option.Some(Seq#Index(_module.DList.s(l'#0), $Unbox(Seq#Index(_module.DList.g(l'#0), p#26)): int)))));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#27: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int } 
              { _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType) } 
            true
               ==> 
              LitInt(0) <= p#27
                 && p#27 < Seq#Length(_module.DList.g(l'#0))
                 && _module.__default.sentinel()
                   <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int
               ==> _module.Node.next($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#27)): DatatypeType)
                 == (if _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int, LitInt(1))
                     < Seq#Length(_module.DList.f(l'#0))
                   then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                      _module.__default.Add($Unbox(Seq#Index(_module.DList.g(l'#0), p#27)): int, LitInt(1)))): int
                   else 0)));
  ensures _module.__default.Inv#canCall(_module._default.InsertBefore$A, l'#0)
     ==> _module.__default.Inv(_module._default.InsertBefore$A, l'#0)
       || (_module.__default.Invs#canCall(_module._default.InsertBefore$A, 
          _module.DList.nodes(l'#0), 
          _module.DList.freeStack(l'#0), 
          _module.DList.s(l'#0), 
          _module.DList.f(l'#0), 
          _module.DList.g(l'#0))
         ==> _module.__default.Invs(_module._default.InsertBefore$A, 
            _module.DList.nodes(l'#0), 
            _module.DList.freeStack(l'#0), 
            _module.DList.s(l'#0), 
            _module.DList.f(l'#0), 
            _module.DList.g(l'#0))
           || (forall p#28: int :: 
            { $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int } 
              { _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#28)): DatatypeType) } 
            true
               ==> (LitInt(0) <= p#28
                     && p#28 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int
                   ==> true)
                 && (LitInt(0) <= p#28
                     && p#28 < Seq#Length(_module.DList.g(l'#0))
                     && _module.__default.sentinel()
                       <= $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int
                   ==> _module.Node.prev($Unbox(Seq#Index(_module.DList.nodes(l'#0), p#28)): DatatypeType)
                     == (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int > 0
                       then $Unbox(Seq#Index(_module.DList.f(l'#0), 
                          _module.__default.Sub($Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int, LitInt(1)))): int
                       else (if $Unbox(Seq#Index(_module.DList.g(l'#0), p#28)): int == LitInt(0)
                           || Seq#Length(_module.DList.f(l'#0)) == LitInt(0)
                         then 0
                         else $Unbox(Seq#Index(_module.DList.f(l'#0), 
                            _module.__default.Sub(Seq#Length(_module.DList.f(l'#0)), LitInt(1)))): int)))));
  free ensures _module.__default.Seq#canCall(_module._default.InsertBefore$A, l'#0)
     && 
    _module.__default.Seq#canCall(_module._default.InsertBefore$A, l#0)
     && _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0)
     && _module.__default.SeqInsert#canCall(_module._default.InsertBefore$A, 
      _module.__default.Seq(_module._default.InsertBefore$A, l#0), 
      _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0), 
      a#0);
  ensures Seq#Equal(_module.__default.Seq(_module._default.InsertBefore$A, l'#0), 
    _module.__default.SeqInsert(_module._default.InsertBefore$A, 
      _module.__default.Seq(_module._default.InsertBefore$A, l#0), 
      _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0), 
      a#0));
  free ensures _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
     && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, p'#0)
       ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
         && _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0));
  ensures _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
     ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, p'#0)
       || 0 < p'#0;
  ensures _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
     ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, p'#0)
       || p'#0 < Seq#Length(_module.DList.g(l'#0));
  ensures _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, p'#0)
     ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, p'#0)
       || $Unbox(Seq#Index(_module.DList.g(l'#0), p'#0)): int >= LitInt(0);
  ensures _module.__default.Index(_module._default.InsertBefore$A, l'#0, p'#0)
     == _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0);
  free ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1) } 
    _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l#0, x#1)
       && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l'#0, x#1))
       && (
        (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
         ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1))
         ==> _module.__default.ValidPtr#canCall(_module._default.InsertBefore$A, l#0, x#1)
           && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
             ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#1)
               && _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0)
               && (_module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
                   < _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
                 ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, x#1)
                   && _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#1))
               && (_module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
                   <= _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
                 ==> _module.__default.Index#canCall(_module._default.InsertBefore$A, l'#0, x#1)
                   && 
                  _module.__default.Index#canCall(_module._default.InsertBefore$A, l#0, x#1)
                   && _module.__default.Add#canCall(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#1), LitInt(1))))));
  ensures (forall x#1: int :: 
    { _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1) } 
      { _module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1) } 
    true
       ==> (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
           ==> _module.__default.ValidPtr(_module._default.InsertBefore$A, l'#0, x#1))
         && (_module.__default.ValidPtr(_module._default.InsertBefore$A, l#0, x#1)
           ==> (if _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
               < _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0)
             then _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1)
               == _module.__default.Index(_module._default.InsertBefore$A, l#0, x#1)
             else _module.__default.Index(_module._default.InsertBefore$A, l'#0, x#1)
               == _module.__default.Add(_module.__default.Index(_module._default.InsertBefore$A, l#0, x#1), LitInt(1)))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.InsertBefore(_module._default.InsertBefore$A: Ty, l#0: DatatypeType, p#0: int, a#0: Box)
   returns (l'#0: DatatypeType, p'#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var freeNode#0: DatatypeType
     where $Is(freeNode#0, Tclass._module.Node(_module._default.InsertBefore$A))
       && $IsAlloc(freeNode#0, Tclass._module.Node(_module._default.InsertBefore$A), $Heap);
  var ##s#1: Seq Box;
  var ##i#0: int;
  var $rhs##0_0: DatatypeType
     where $Is($rhs##0_0, Tclass._module.DList(_module._default.InsertBefore$A))
       && $IsAlloc($rhs##0_0, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
  var l##0_0: DatatypeType;
  var ##s#0_0: Seq Box;
  var ##i#0_0: int;
  var nodes#0: Seq Box;
  var freeStack#0: int;
  var s#0: Seq Box;
  var f#0: Seq Box;
  var g#0: Seq Box;
  var let#0#0#0: DatatypeType;
  var index'#0: int;
  var ##l#17: DatatypeType;
  var ##p#13: int;
  var s'#0: Seq Box
     where $Is(s'#0, TSeq(_module._default.InsertBefore$A))
       && $IsAlloc(s'#0, TSeq(_module._default.InsertBefore$A), $Heap);
  var ##s#2: Seq Box;
  var ##k#1: int;
  var ##v#1: Box;
  var f'#0: Seq Box where $Is(f'#0, TSeq(TInt)) && $IsAlloc(f'#0, TSeq(TInt), $Heap);
  var ##s#3: Seq Box;
  var ##k#2: int;
  var ##v#2: int;
  var g'#0: Seq Box where $Is(g'#0, TSeq(TInt)) && $IsAlloc(g'#0, TSeq(TInt), $Heap);
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var g##0: Seq Box;
  var p'##0: int;
  var index'##0: int;
  var node#0: DatatypeType
     where $Is(node#0, Tclass._module.Node(_module._default.InsertBefore$A))
       && $IsAlloc(node#0, Tclass._module.Node(_module._default.InsertBefore$A), $Heap);
  var ##s#4: Seq Box;
  var ##i#1: int;
  var node'#0: DatatypeType
     where $Is(node'#0, Tclass._module.Node(_module._default.InsertBefore$A))
       && $IsAlloc(node'#0, Tclass._module.Node(_module._default.InsertBefore$A), $Heap);
  var dt_update_tmp#0#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var dt_update#prev#0#0: int;
  var let#2#0#0: int;
  var ##s1#0: Seq Box;
  var ##i#2: int;
  var ##a#1: DatatypeType;
  var node_prev#0: DatatypeType
     where $Is(node_prev#0, Tclass._module.Node(_module._default.InsertBefore$A))
       && $IsAlloc(node_prev#0, Tclass._module.Node(_module._default.InsertBefore$A), $Heap);
  var ##s#5: Seq Box;
  var ##i#3: int;
  var dt_update_tmp#1#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var dt_update#next#0#0: int;
  var let#4#0#0: int;
  var ##s1#1: Seq Box;
  var ##i#4: int;
  var ##a#2: DatatypeType;
  var ##s1#2: Seq Box;
  var ##i#5: int;
  var ##a#3: DatatypeType;

    // AddMethodImpl: InsertBefore, Impl$$_module.__default.InsertBefore
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(361,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- DLL_Dafny.dfy(362,6)
    assume true;
    assume true;
    l'#0 := l#0;
    assume {:captureState "DLL_Dafny.dfy(362,9)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(363,6)
    assume true;
    assume _module.DList.DList_q(l'#0);
    assume _module.DList.DList_q(l'#0);
    p'#0 := _module.DList.freeStack(l'#0);
    assume {:captureState "DLL_Dafny.dfy(363,20)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(364,16)
    assume true;
    assume _module.DList.DList_q(l'#0);
    ##s#1 := _module.DList.nodes(l'#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
    ##i#0 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#0;
    assert {:subsumption 0} ##i#0 < Seq#Length(##s#1);
    assume LitInt(0) <= ##i#0 && ##i#0 < Seq#Length(##s#1);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
      _module.DList.nodes(l'#0), 
      p'#0);
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), 
          _module.DList.nodes(l'#0), 
          p'#0)): DatatypeType);
    assume _module.DList.DList_q(l'#0)
       && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
        _module.DList.nodes(l'#0), 
        p'#0);
    freeNode#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), 
        _module.DList.nodes(l'#0), 
        p'#0)): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(364,39)"} true;
    // ----- if statement ----- DLL_Dafny.dfy(365,3)
    if (p'#0 != LitInt(0))
    {
        assume _module.Node.Node_q(freeNode#0);
    }

    assume p'#0 != LitInt(0) ==> _module.Node.Node_q(freeNode#0);
    if (p'#0 == LitInt(0) || _module.Option.Some_q(_module.Node.data(freeNode#0)))
    {
        // ----- call statement ----- DLL_Dafny.dfy(366,17)
        assume true;
        // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<A>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        l##0_0 := l'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.__default.Expand(_module._default.InsertBefore$A, l##0_0);
        // TrCallStmt: After ProcessCallStmt
        l'#0 := $rhs##0_0;
        assume {:captureState "DLL_Dafny.dfy(366,20)"} true;
        // ----- assignment statement ----- DLL_Dafny.dfy(367,8)
        assume true;
        assume _module.DList.DList_q(l'#0);
        assume _module.DList.DList_q(l'#0);
        p'#0 := _module.DList.freeStack(l'#0);
        assume {:captureState "DLL_Dafny.dfy(367,22)"} true;
        // ----- assignment statement ----- DLL_Dafny.dfy(368,14)
        assume true;
        assume _module.DList.DList_q(l'#0);
        ##s#0_0 := _module.DList.nodes(l'#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
        ##i#0_0 := p'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##i#0_0, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##i#0_0;
        assert {:subsumption 0} ##i#0_0 < Seq#Length(##s#0_0);
        assume LitInt(0) <= ##i#0_0 && ##i#0_0 < Seq#Length(##s#0_0);
        assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
          _module.DList.nodes(l'#0), 
          p'#0);
        assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), 
              _module.DList.nodes(l'#0), 
              p'#0)): DatatypeType);
        assume _module.DList.DList_q(l'#0)
           && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
            _module.DList.nodes(l'#0), 
            p'#0);
        freeNode#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), 
            _module.DList.nodes(l'#0), 
            p'#0)): DatatypeType;
        assume {:captureState "DLL_Dafny.dfy(368,37)"} true;
    }
    else
    {
    }

    havoc nodes#0;
    assume $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)))
       && $IsAlloc(nodes#0, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
    havoc freeStack#0;
    havoc s#0;
    assume $Is(s#0, TSeq(_module._default.InsertBefore$A))
       && $IsAlloc(s#0, TSeq(_module._default.InsertBefore$A), $Heap);
    havoc f#0;
    assume $Is(f#0, TSeq(TInt)) && $IsAlloc(f#0, TSeq(TInt), $Heap);
    havoc g#0;
    assume $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap);
    assume let#0#0#0 == l'#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.DList(_module._default.InsertBefore$A));
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume #_module.DList.DList(nodes#0, freeStack#0, s#0, f#0, g#0) == let#0#0#0;
    // ----- assignment statement ----- DLL_Dafny.dfy(371,20)
    assume true;
    ##l#17 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#17, Tclass._module.DList(_module._default.InsertBefore$A), $Heap);
    ##p#13 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#13, TInt, $Heap);
    assume _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0);
    assume _module.__default.IndexHi#canCall(_module._default.InsertBefore$A, l#0, p#0);
    index'#0 := _module.__default.IndexHi(_module._default.InsertBefore$A, l#0, p#0);
    assume {:captureState "DLL_Dafny.dfy(371,35)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(372,16)
    assume true;
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, TSeq(_module._default.InsertBefore$A), $Heap);
    ##k#1 := index'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#1, TInt, $Heap);
    ##v#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##v#1, _module._default.InsertBefore$A, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#1;
    assert {:subsumption 0} ##k#1 <= Seq#Length(##s#2);
    assume LitInt(0) <= ##k#1 && ##k#1 <= Seq#Length(##s#2);
    assume _module.__default.SeqInsert#canCall(_module._default.InsertBefore$A, s#0, index'#0, a#0);
    assume _module.__default.SeqInsert#canCall(_module._default.InsertBefore$A, s#0, index'#0, a#0);
    s'#0 := _module.__default.SeqInsert(_module._default.InsertBefore$A, s#0, index'#0, a#0);
    assume {:captureState "DLL_Dafny.dfy(372,41)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(373,16)
    assume true;
    ##s#3 := f#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, TSeq(TInt), $Heap);
    ##k#2 := index'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#2, TInt, $Heap);
    ##v#2 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##v#2, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##k#2;
    assert {:subsumption 0} ##k#2 <= Seq#Length(##s#3);
    assume LitInt(0) <= ##k#2 && ##k#2 <= Seq#Length(##s#3);
    assume _module.__default.SeqInsert#canCall(TInt, f#0, index'#0, $Box(p'#0));
    assume _module.__default.SeqInsert#canCall(TInt, f#0, index'#0, $Box(p'#0));
    f'#0 := _module.__default.SeqInsert(TInt, f#0, index'#0, $Box(p'#0));
    assume {:captureState "DLL_Dafny.dfy(373,42)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(374,39)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type seq<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    g##0 := g#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p'##0 := p'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    index'##0 := index'#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.InsertBefore__SeqInit(g##0, p'##0, index'##0);
    // TrCallStmt: After ProcessCallStmt
    g'#0 := $rhs##0;
    assume {:captureState "DLL_Dafny.dfy(374,53)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(375,12)
    assume true;
    ##s#4 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#4, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
    ##i#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#1;
    assert {:subsumption 0} ##i#1 < Seq#Length(##s#4);
    assume LitInt(0) <= ##i#1 && ##i#1 < Seq#Length(##s#4);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), nodes#0, p#0);
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), nodes#0, p#0)): DatatypeType);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), nodes#0, p#0);
    node#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), nodes#0, p#0)): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(375,31)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(376,13)
    assume true;
    assume _module.Node.Node_q(node#0);
    assume _module.Node.Node_q(node#0);
    node'#0 := #_module.Node.Node(#_module.Option.Some(a#0), p#0, _module.Node.prev(node#0));
    assume {:captureState "DLL_Dafny.dfy(376,42)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(377,9)
    assume true;
    havoc dt_update_tmp#0#0;
    assume $Is(dt_update_tmp#0#0, Tclass._module.Node(_module._default.InsertBefore$A));
    assume let#1#0#0 == node#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, Tclass._module.Node(_module._default.InsertBefore$A));
    assume dt_update_tmp#0#0 == let#1#0#0;
    havoc dt_update#prev#0#0;
    assume let#2#0#0 == p'#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#2#0#0, TInt);
    assume dt_update#prev#0#0 == let#2#0#0;
    assume _module.Node.Node_q(dt_update_tmp#0#0);
    assume _module.Node.Node_q(dt_update_tmp#0#0);
    ##s1#0 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#0, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
    ##i#2 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#2, TInt, $Heap);
    ##a#1 := (var dt_update_tmp#0#1 := node#0; 
      (var dt_update#prev#0#1 := p'#0; 
        #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
          _module.Node.next(dt_update_tmp#0#1), 
          dt_update#prev#0#1)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, Tclass._module.Node(_module._default.InsertBefore$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#2;
    assert {:subsumption 0} ##i#2 < Seq#Length(##s1#0);
    assume LitInt(0) <= ##i#2 && ##i#2 < Seq#Length(##s1#0);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      p#0, 
      $Box((var dt_update_tmp#0#1 := node#0; 
          (var dt_update#prev#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
              _module.Node.next(dt_update_tmp#0#1), 
              dt_update#prev#0#1)))));
    assume (var dt_update_tmp#0#1 := node#0; 
        _module.Node.Node_q(dt_update_tmp#0#1) && _module.Node.Node_q(dt_update_tmp#0#1))
       && _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
        nodes#0, 
        p#0, 
        $Box((var dt_update_tmp#0#1 := node#0; 
            (var dt_update#prev#0#1 := p'#0; 
              #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
                _module.Node.next(dt_update_tmp#0#1), 
                dt_update#prev#0#1)))));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      p#0, 
      $Box((var dt_update_tmp#0#1 := node#0; 
          (var dt_update#prev#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#0#1), 
              _module.Node.next(dt_update_tmp#0#1), 
              dt_update#prev#0#1)))));
    assume {:captureState "DLL_Dafny.dfy(377,47)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(378,17)
    assume true;
    assume _module.Node.Node_q(node#0);
    ##s#5 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#5, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
    ##i#3 := _module.Node.prev(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#3;
    assert {:subsumption 0} ##i#3 < Seq#Length(##s#5);
    assume LitInt(0) <= ##i#3 && ##i#3 < Seq#Length(##s#5);
    assume _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      _module.Node.prev(node#0));
    assume _module.Node.Node_q($Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), 
          nodes#0, 
          _module.Node.prev(node#0))): DatatypeType);
    assume _module.Node.Node_q(node#0)
       && _module.__default.seq__get#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
        nodes#0, 
        _module.Node.prev(node#0));
    node_prev#0 := $Unbox(_module.__default.seq__get(Tclass._module.Node(_module._default.InsertBefore$A), 
        nodes#0, 
        _module.Node.prev(node#0))): DatatypeType;
    assume {:captureState "DLL_Dafny.dfy(378,44)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(379,9)
    assume true;
    assume _module.Node.Node_q(node#0);
    havoc dt_update_tmp#1#0;
    assume $Is(dt_update_tmp#1#0, Tclass._module.Node(_module._default.InsertBefore$A));
    assume let#3#0#0 == node_prev#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#3#0#0, Tclass._module.Node(_module._default.InsertBefore$A));
    assume dt_update_tmp#1#0 == let#3#0#0;
    havoc dt_update#next#0#0;
    assume let#4#0#0 == p'#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#4#0#0, TInt);
    assume dt_update#next#0#0 == let#4#0#0;
    assume _module.Node.Node_q(dt_update_tmp#1#0);
    assume _module.Node.Node_q(dt_update_tmp#1#0);
    ##s1#1 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#1, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
    ##i#4 := _module.Node.prev(node#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#4, TInt, $Heap);
    ##a#2 := (var dt_update_tmp#1#1 := node_prev#0; 
      (var dt_update#next#0#1 := p'#0; 
        #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
          dt_update#next#0#1, 
          _module.Node.prev(dt_update_tmp#1#1))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, Tclass._module.Node(_module._default.InsertBefore$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#4;
    assert {:subsumption 0} ##i#4 < Seq#Length(##s1#1);
    assume LitInt(0) <= ##i#4 && ##i#4 < Seq#Length(##s1#1);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      _module.Node.prev(node#0), 
      $Box((var dt_update_tmp#1#1 := node_prev#0; 
          (var dt_update#next#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
              dt_update#next#0#1, 
              _module.Node.prev(dt_update_tmp#1#1))))));
    assume _module.Node.Node_q(node#0)
       && (var dt_update_tmp#1#1 := node_prev#0; 
        _module.Node.Node_q(dt_update_tmp#1#1) && _module.Node.Node_q(dt_update_tmp#1#1))
       && _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
        nodes#0, 
        _module.Node.prev(node#0), 
        $Box((var dt_update_tmp#1#1 := node_prev#0; 
            (var dt_update#next#0#1 := p'#0; 
              #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
                dt_update#next#0#1, 
                _module.Node.prev(dt_update_tmp#1#1))))));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      _module.Node.prev(node#0), 
      $Box((var dt_update_tmp#1#1 := node_prev#0; 
          (var dt_update#next#0#1 := p'#0; 
            #_module.Node.Node(_module.Node.data(dt_update_tmp#1#1), 
              dt_update#next#0#1, 
              _module.Node.prev(dt_update_tmp#1#1))))));
    assume {:captureState "DLL_Dafny.dfy(379,60)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(380,9)
    assume true;
    ##s1#2 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s1#2, TSeq(Tclass._module.Node(_module._default.InsertBefore$A)), $Heap);
    ##i#5 := p'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##i#5, TInt, $Heap);
    ##a#3 := node'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, Tclass._module.Node(_module._default.InsertBefore$A), $Heap);
    assert {:subsumption 0} LitInt(0) <= ##i#5;
    assert {:subsumption 0} ##i#5 < Seq#Length(##s1#2);
    assume LitInt(0) <= ##i#5 && ##i#5 < Seq#Length(##s1#2);
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      p'#0, 
      $Box(node'#0));
    assume _module.__default.seq__set#canCall(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      p'#0, 
      $Box(node'#0));
    nodes#0 := _module.__default.seq__set(Tclass._module.Node(_module._default.InsertBefore$A), 
      nodes#0, 
      p'#0, 
      $Box(node'#0));
    assume {:captureState "DLL_Dafny.dfy(380,36)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(381,6)
    assume true;
    assume _module.Node.Node_q(freeNode#0);
    assume _module.Node.Node_q(freeNode#0);
    l'#0 := #_module.DList.DList(nodes#0, _module.Node.next(freeNode#0), s'#0, f'#0, g'#0);
    assume {:captureState "DLL_Dafny.dfy(381,47)"} true;
}



procedure CheckWellformed$$_module.__default.Clone(_module._default.Clone$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Clone$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Clone$A), $Heap)
         && $IsA#_module.DList(l#0))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Clone$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Clone$A), $Heap));
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Clone(_module._default.Clone$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Clone$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Clone$A), $Heap)
         && $IsA#_module.DList(l#0))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Clone$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Clone$A), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.DList(l'#0) && $IsA#_module.DList(l#0);
  ensures _module.DList#Equal(l'#0, l#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Clone(_module._default.Clone$A: Ty, 
    l#0: DatatypeType
       where $Is(l#0, Tclass._module.DList(_module._default.Clone$A))
         && $IsAlloc(l#0, Tclass._module.DList(_module._default.Clone$A), $Heap)
         && $IsA#_module.DList(l#0))
   returns (l'#0: DatatypeType
       where $Is(l'#0, Tclass._module.DList(_module._default.Clone$A))
         && $IsAlloc(l'#0, Tclass._module.DList(_module._default.Clone$A), $Heap), 
    $_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.DList(l'#0) && $IsA#_module.DList(l#0);
  ensures _module.DList#Equal(l'#0, l#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Clone(_module._default.Clone$A: Ty, l#0: DatatypeType)
   returns (l'#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var nodes#0: Seq Box;
  var freeStack#0: int;
  var s#0: Seq Box;
  var f#0: Seq Box;
  var g#0: Seq Box;
  var let#0#0#0: DatatypeType;
  var nodes'#0: Seq Box
     where $Is(nodes'#0, TSeq(Tclass._module.Node(_module._default.Clone$A)))
       && $IsAlloc(nodes'#0, TSeq(Tclass._module.Node(_module._default.Clone$A)), $Heap);
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(Tclass._module.Node(_module._default.Clone$A)))
       && $IsAlloc($rhs##0, TSeq(Tclass._module.Node(_module._default.Clone$A)), $Heap);
  var source##0: Seq Box;
  var from##0: int;
  var to##0: int;
  var ##s#0: Seq Box;

    // AddMethodImpl: Clone, Impl$$_module.__default.Clone
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(386,0): initial state"} true;
    $_reverifyPost := false;
    havoc nodes#0;
    assume $Is(nodes#0, TSeq(Tclass._module.Node(_module._default.Clone$A)))
       && $IsAlloc(nodes#0, TSeq(Tclass._module.Node(_module._default.Clone$A)), $Heap);
    havoc freeStack#0;
    havoc s#0;
    assume $Is(s#0, TSeq(_module._default.Clone$A))
       && $IsAlloc(s#0, TSeq(_module._default.Clone$A), $Heap);
    havoc f#0;
    assume $Is(f#0, TSeq(TInt)) && $IsAlloc(f#0, TSeq(TInt), $Heap);
    havoc g#0;
    assume $Is(g#0, TSeq(TInt)) && $IsAlloc(g#0, TSeq(TInt), $Heap);
    assume let#0#0#0 == l#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.DList(_module._default.Clone$A));
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume _module.DList.DList_q(let#0#0#0);
    assume #_module.DList.DList(nodes#0, freeStack#0, s#0, f#0, g#0) == let#0#0#0;
    // ----- call statement ----- DLL_Dafny.dfy(389,29)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type seq<Node<A>>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    source##0 := nodes#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    from##0 := LitInt(0);
    ##s#0 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(Tclass._module.Node(_module._default.Clone$A)), $Heap);
    assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.Clone$A), nodes#0);
    assume _module.__default.seq_length#canCall(Tclass._module.Node(_module._default.Clone$A), nodes#0);
    // ProcessCallStmt: CheckSubrange
    to##0 := _module.__default.seq_length(Tclass._module.Node(_module._default.Clone$A), nodes#0);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.AllocAndCopy(Tclass._module.Node(_module._default.Clone$A), source##0, from##0, to##0);
    // TrCallStmt: After ProcessCallStmt
    nodes'#0 := $rhs##0;
    assume {:captureState "DLL_Dafny.dfy(389,57)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(390,6)
    assume true;
    assume true;
    l'#0 := #_module.DList.DList(nodes'#0, freeStack#0, s#0, f#0, g#0);
    assume {:captureState "DLL_Dafny.dfy(390,41)"} true;
}



procedure CheckWellformed$$_module.__default.main();
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.main();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.main() returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.main() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var l#0: DatatypeType
     where $Is(l#0, Tclass._module.DList(TInt))
       && $IsAlloc(l#0, Tclass._module.DList(TInt), $Heap);
  var $rhs##0: DatatypeType
     where $Is($rhs##0, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##0, Tclass._module.DList(TInt), $Heap);
  var initial_len##0: int;
  var p#0: int;
  var $rhs##1: DatatypeType
     where $Is($rhs##1, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##1, Tclass._module.DList(TInt), $Heap);
  var $rhs##2: int;
  var l##0: DatatypeType;
  var p##0: int;
  var a##0: Box;
  var $rhs##3: DatatypeType
     where $Is($rhs##3, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##3, Tclass._module.DList(TInt), $Heap);
  var $rhs##4: int;
  var l##1: DatatypeType;
  var p##1: int;
  var a##1: Box;
  var $rhs##5: DatatypeType
     where $Is($rhs##5, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##5, Tclass._module.DList(TInt), $Heap);
  var $rhs##6: int;
  var l##2: DatatypeType;
  var p##2: int;
  var a##2: Box;
  var p3#0: int;
  var $rhs##7: DatatypeType
     where $Is($rhs##7, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##7, Tclass._module.DList(TInt), $Heap);
  var $rhs##8: int;
  var l##3: DatatypeType;
  var p##3: int;
  var a##3: Box;
  var $rhs##9: DatatypeType
     where $Is($rhs##9, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##9, Tclass._module.DList(TInt), $Heap);
  var $rhs##10: int;
  var l##4: DatatypeType;
  var p##4: int;
  var a##4: Box;
  var ##l#0: DatatypeType;
  var $rhs##11: DatatypeType
     where $Is($rhs##11, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##11, Tclass._module.DList(TInt), $Heap);
  var l##5: DatatypeType;
  var p##5: int;
  var ##l#1: DatatypeType;
  var $rhs##12: DatatypeType
     where $Is($rhs##12, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##12, Tclass._module.DList(TInt), $Heap);
  var $rhs##13: int;
  var l##6: DatatypeType;
  var p##6: int;
  var a##5: Box;
  var $rhs##14: DatatypeType
     where $Is($rhs##14, Tclass._module.DList(TInt))
       && $IsAlloc($rhs##14, Tclass._module.DList(TInt), $Heap);
  var $rhs##15: int;
  var l##7: DatatypeType;
  var p##7: int;
  var a##6: Box;
  var ##l#2: DatatypeType;
  var l##8: DatatypeType;

    // AddMethodImpl: main, Impl$$_module.__default.main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "DLL_Dafny.dfy(395,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- DLL_Dafny.dfy(396,22)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type DList<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    initial_len##0 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.Alloc(TInt, initial_len##0);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##0;
    assume {:captureState "DLL_Dafny.dfy(396,24)"} true;
    havoc p#0;
    // ----- call statement ----- DLL_Dafny.dfy(398,22)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##0 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##0 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := $Box(LitInt(100));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1, $rhs##2 := Call$$_module.__default.InsertAfter(TInt, l##0, p##0, a##0);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##1;
    p#0 := $rhs##2;
    assume {:captureState "DLL_Dafny.dfy(398,32)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(399,22)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##1 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##1 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := $Box(LitInt(200));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##3, $rhs##4 := Call$$_module.__default.InsertAfter(TInt, l##1, p##1, a##1);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##3;
    p#0 := $rhs##4;
    assume {:captureState "DLL_Dafny.dfy(399,32)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(400,22)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##2 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##2 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##2 := $Box(LitInt(300));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##5, $rhs##6 := Call$$_module.__default.InsertAfter(TInt, l##2, p##2, a##2);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##5;
    p#0 := $rhs##6;
    assume {:captureState "DLL_Dafny.dfy(400,32)"} true;
    // ----- assignment statement ----- DLL_Dafny.dfy(401,10)
    assume true;
    assume true;
    p3#0 := p#0;
    assume {:captureState "DLL_Dafny.dfy(401,13)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(402,22)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##3 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##3 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##3 := $Box(LitInt(400));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##7, $rhs##8 := Call$$_module.__default.InsertAfter(TInt, l##3, p##3, a##3);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##7;
    p#0 := $rhs##8;
    assume {:captureState "DLL_Dafny.dfy(402,32)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(403,22)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##4 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##4 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##4 := $Box(LitInt(500));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##9, $rhs##10 := Call$$_module.__default.InsertAfter(TInt, l##4, p##4, a##4);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##9;
    p#0 := $rhs##10;
    assume {:captureState "DLL_Dafny.dfy(403,32)"} true;
    // ----- assert statement ----- DLL_Dafny.dfy(404,3)
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.DList(TInt), $Heap);
    assume _module.__default.Seq#canCall(TInt, l#0);
    assume _module.__default.Seq#canCall(TInt, l#0);
    assert Seq#Equal(_module.__default.Seq(TInt, l#0), 
      Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(100))), $Box(LitInt(200))), 
            $Box(LitInt(300))), 
          $Box(LitInt(400))), 
        $Box(LitInt(500))));
    // ----- call statement ----- DLL_Dafny.dfy(405,14)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##5 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##5 := p3#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##11 := Call$$_module.__default.Remove(TInt, l##5, p##5);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##11;
    assume {:captureState "DLL_Dafny.dfy(405,20)"} true;
    // ----- assert statement ----- DLL_Dafny.dfy(406,3)
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.DList(TInt), $Heap);
    assume _module.__default.Seq#canCall(TInt, l#0);
    assume _module.__default.Seq#canCall(TInt, l#0);
    assert Seq#Equal(_module.__default.Seq(TInt, l#0), 
      Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(100))), $Box(LitInt(200))), 
          $Box(LitInt(400))), 
        $Box(LitInt(500))));
    // ----- call statement ----- DLL_Dafny.dfy(407,22)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##6 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##6 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##5 := $Box(LitInt(600));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##12, $rhs##13 := Call$$_module.__default.InsertAfter(TInt, l##6, p##6, a##5);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##12;
    p#0 := $rhs##13;
    assume {:captureState "DLL_Dafny.dfy(407,32)"} true;
    // ----- call statement ----- DLL_Dafny.dfy(408,22)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type DList<int>
    // TrCallStmt: Adding lhs Microsoft.Dafny.IdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##7 := l#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##7 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##6 := $Box(LitInt(700));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##14, $rhs##15 := Call$$_module.__default.InsertAfter(TInt, l##7, p##7, a##6);
    // TrCallStmt: After ProcessCallStmt
    l#0 := $rhs##14;
    p#0 := $rhs##15;
    assume {:captureState "DLL_Dafny.dfy(408,32)"} true;
    // ----- assert statement ----- DLL_Dafny.dfy(409,3)
    ##l#2 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#2, Tclass._module.DList(TInt), $Heap);
    assume _module.__default.Seq#canCall(TInt, l#0);
    assume _module.__default.Seq#canCall(TInt, l#0);
    assert Seq#Equal(_module.__default.Seq(TInt, l#0), 
      Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(100))), $Box(LitInt(200))), 
              $Box(LitInt(400))), 
            $Box(LitInt(500))), 
          $Box(LitInt(600))), 
        $Box(LitInt(700))));
    // ----- call statement ----- DLL_Dafny.dfy(410,7)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##8 := l#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Free(TInt, l##8);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "DLL_Dafny.dfy(410,9)"} true;
}


