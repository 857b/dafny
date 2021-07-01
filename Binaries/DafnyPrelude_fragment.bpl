// Dafny prelude - FRAGMENT
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

const $$Language$Dafny: bool;  // To be recognizable to the ModelViewer as
// AxLangDafny
axiom $$Language$Dafny;        // coming from a Dafny program.

// ---------------------------------------------------------------
// -- Types ---------------------------------------------------{{{
// ---------------------------------------------------------------

type Ty;
type Bv0;

const unique TBool : Ty;
const unique TInt  : Ty;


// -- Classes and Datatypes --

// -- Type Tags --
type TyTag;
function Tag(Ty) : TyTag;

const unique TagBool     : TyTag;
const unique TagInt      : TyTag;
const unique TagClass    : TyTag;

axiom Tag(TBool) == TagBool;
axiom Tag(TInt) == TagInt;

type TyTagFamily;
function TagFamily(Ty): TyTagFamily;

// }}}------------------------------------------------------------
// -- Literals ------------------------------------------------{{{
// ---------------------------------------------------------------
function {:identity} Lit<T>(x: T): T { x }
// AxBoxLit
axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );

// Specialize Lit to concrete types.
// These aren't logically required, but on some examples improve
// verification speed
function {:identity} LitInt(x: int): int { x }
// AxBoxLitInt
axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)) );

// }}}------------------------------------------------------------
// -- Characters ----------------------------------------------{{{
// ---------------------------------------------------------------

type char;
// }}}------------------------------------------------------------
// -- References ----------------------------------------------{{{
// ---------------------------------------------------------------

type ref;
const null: ref;

// }}}------------------------------------------------------------
// -- Boxing and unboxing -------------------------------------{{{
// ---------------------------------------------------------------

type Box;
const $ArbitraryBoxValue: Box;

function $Box<T>(T): Box;
function $Unbox<T>(Box): T;

// AxUnboxBox
axiom (forall<T> x : T :: { $Box(x) } $Unbox($Box(x)) == x);

// AxIsBoxInt
axiom (forall bx : Box ::
    { $IsBox(bx, TInt) }
    ( $IsBox(bx, TInt) ==> $Box($Unbox(bx) : int) == bx && $Is($Unbox(bx) : int, TInt)));
// AxIsBoxBool
axiom (forall bx : Box ::
    { $IsBox(bx, TBool) }
    ( $IsBox(bx, TBool) ==> $Box($Unbox(bx) : bool) == bx && $Is($Unbox(bx) : bool, TBool)));

// AxIsBoxBox
axiom (forall<T> v : T, t : Ty ::
    { $IsBox($Box(v), t) }
    ( $IsBox($Box(v), t) <==> $Is(v,t) ));
// AxIsAllocBoxBox
axiom (forall<T> v : T, t : Ty, h : Heap ::
    { $IsAllocBox($Box(v), t, h) }
    ( $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v,t,h) ));

// }}}------------------------------------------------------------
// -- Is and IsAlloc ------------------------------------------{{{
// ---------------------------------------------------------------

// Type-argument to $Is is the /representation type/,
// the second value argument to $Is is the actual type.
function $Is<T>(T,Ty): bool;           // no heap for now
function $IsAlloc<T>(T,Ty,Heap): bool;

// Corresponding entries for boxes...
// This could probably be solved by having Box also inhabit Ty
function $IsBox<T>(T,Ty): bool;
function $IsAllocBox<T>(T,Ty,Heap): bool;

// AxIsInt
axiom(forall v : int  :: { $Is(v,TInt) }  $Is(v,TInt));
// AxIsBool
axiom(forall v : bool :: { $Is(v,TBool) } $Is(v,TBool));

// AxIsAllocInt
axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TInt,h) }  $IsAlloc(v,TInt,h));
// AxIsAllocBool
axiom(forall h : Heap, v : bool :: { $IsAlloc(v,TBool,h) } $IsAlloc(v,TBool,h));

// }}}------------------------------------------------------------
// -- Encoding of type names ----------------------------------{{{
// ---------------------------------------------------------------

type ClassName;
const unique class._System.int: ClassName;
const unique class._System.bool: ClassName;

function Tclass._System.object?(): Ty;
function Tclass._System.Tuple2(Ty, Ty): Ty;

function /*{:never_pattern true}*/ dtype(ref): Ty; // changed from ClassName to Ty

// -- Function handles -------------------------------------------

type HandleType;

// Functions ApplyN, RequiresN, and ReadsN are generated on demand by the translator,
// but Apply1 is referred to in the prelude, so its definition is hardcoded here.
function Apply1(Ty, Ty, Heap, HandleType, Box): Box;

// }}}------------------------------------------------------------
// -- Datatypes -----------------------------------------------{{{
// ---------------------------------------------------------------

type DatatypeType;

type DtCtorId;
function DatatypeCtorId(DatatypeType): DtCtorId;

function DtRank(DatatypeType): int;
function BoxRank(Box): int;
// }}}------------------------------------------------------------
// -- Big Ordinals --------------------------------------------{{{
// ---------------------------------------------------------------

type ORDINAL;

function ORD#IsNat(ORDINAL): bool;
function ORD#Offset(ORDINAL): int;

function ORD#IsLimit(o: ORDINAL): bool;
function ORD#IsSucc(o: ORDINAL): bool;

// }}}------------------------------------------------------------
// -- Axiom contexts ------------------------------------------{{{
// ---------------------------------------------------------------

// used to make sure function axioms are not used while their consistency is being checked
const $FunctionContextHeight: int;

// }}}------------------------------------------------------------
// -- Layers of function encodings ----------------------------{{{
// ---------------------------------------------------------------

type LayerType;

// }}}------------------------------------------------------------
// -- Fields --------------------------------------------------{{{
// ---------------------------------------------------------------

type Field alpha;

function FDim<T>(Field T): int;

function IndexField(int): Field Box;
function DeclType<T>(Field T): ClassName;

type NameFamily;
function DeclName<T>(Field T): NameFamily;
function FieldOfDecl<alpha>(ClassName, NameFamily): Field alpha;
// AxFieldOfDeclRec-
axiom (forall<T> cl : ClassName, nm: NameFamily ::
   {FieldOfDecl(cl, nm): Field T}
   DeclType(FieldOfDecl(cl, nm): Field T) == cl && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

function $IsGhostField<T>(Field T): bool;

// }}}------------------------------------------------------------
// -- Allocatedness and Heap Succession -----------------------{{{
// ---------------------------------------------------------------


// $IsAlloc and $IsAllocBox are monotonic

// AxHeapSuccIsAlloc
axiom(forall<T> h, k : Heap, v : T, t : Ty ::
  { $HeapSucc(h, k), $IsAlloc(v, t, h) }
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));
// AxHeapSuccIsAllocBox
axiom(forall h, k : Heap, bx : Box, t : Ty ::
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) }
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

// No axioms for $Is and $IsBox since they don't talk about the heap.

const unique alloc: Field bool;
const unique allocName: NameFamily;
axiom FDim(alloc) == 0 &&
  DeclName(alloc) == allocName &&
  !$IsGhostField(alloc);  // treat as non-ghost field, because it cannot be changed by ghost code

// }}}------------------------------------------------------------
// -- Arrays --------------------------------------------------{{{
// ---------------------------------------------------------------

function _System.array.Length(a: ref): int;

// }}}------------------------------------------------------------
// -- Reals ---------------------------------------------------{{{
// ---------------------------------------------------------------

function _System.real.Floor(): bool; // PLACEHOLDER

// }}}------------------------------------------------------------
// -- The heap ------------------------------------------------{{{
// ---------------------------------------------------------------
type Heap = [ref]<alpha>[Field alpha]alpha;
function {:inline} read<alpha>(H:Heap, r:ref, f:Field alpha): alpha { H[r][f] }
function {:inline} update<alpha>(H:Heap, r:ref, f:Field alpha, v:alpha): Heap { H[r := H[r][f := v]] }

function $IsGoodHeap(Heap): bool;
function $IsHeapAnchor(Heap): bool;
var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

// The following is used as a reference heap in places where the translation needs a heap
// but the expression generated is really one that is (at least in a correct program)
// independent of the heap.
const $OneHeap: Heap;
// AxOneHeapGood-
axiom $IsGoodHeap($OneHeap);

function $HeapSucc(Heap, Heap): bool;
// AxUpdtHeapSucc
axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: { update(h, r, f, x) }
  $IsGoodHeap(update(h, r, f, x)) ==>
  $HeapSucc(h, update(h, r, f, x)));
// AxHeapSuccTrans
axiom (forall a,b,c: Heap :: { $HeapSucc(a,b), $HeapSucc(b,c) }
  a != c ==> $HeapSucc(a,b) && $HeapSucc(b,c) ==> $HeapSucc(a,c));
// AxHeapSuccAlloc
axiom (forall h: Heap, k: Heap :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

// }}}------------------------------------------------------------
// -- Non-determinism -----------------------------------------{{{
// ---------------------------------------------------------------

type TickType;
var $Tick: TickType;

// }}}------------------------------------------------------------
// -- Axiomatizations -----------------------------------------{{{
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// -- Axiomatization of sets ----------------------------------{{{
// ---------------------------------------------------------------

type Set T;

function Set#Empty<T>(): Set T;
function Set#Equal<T>(Set T, Set T): bool;
// }}}------------------------------------------------------------
// -- Axiomatization of isets ---------------------------------{{{
// ---------------------------------------------------------------

type ISet T;

// }}}------------------------------------------------------------
// -- Axiomatization of multisets -----------------------------{{{
// ---------------------------------------------------------------

type MultiSet T;

// }}}------------------------------------------------------------
// -- Axiomatization of sequences -----------------------------{{{
// ---------------------------------------------------------------

type Seq T;

// }}}------------------------------------------------------------
// -- Axiomatization of Maps ----------------------------------{{{
// ---------------------------------------------------------------

type Map U V;

function Map#Domain<U,V>(Map U V) : Set U;

function Map#Values<U,V>(Map U V) : Set V;

function Map#Items<U,V>(Map U V) : Set Box;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;
function _System.Tuple2._0(DatatypeType) : Box;
function _System.Tuple2._1(DatatypeType) : Box;

// }}}------------------------------------------------------------
// -- Axiomatization of IMaps ---------------------------------{{{
// ---------------------------------------------------------------

type IMap U V;

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Values<U,V>(IMap U V) : Set V;

function IMap#Items<U,V>(IMap U V) : Set Box;

// }}}-}}}------------------------------------------------------------------
// -- Provide arithmetic wrappers to improve triggering and non-linear math {{{
// -------------------------------------------------------------------------

// }}}------------------------------------------------------------
// -- BuiltIns declarations -----------------------------------{{{
// ---------------------------------------------------------------

function Tclass._System.array?(Ty) : Ty;

// }}}------------------------------------------------------------
