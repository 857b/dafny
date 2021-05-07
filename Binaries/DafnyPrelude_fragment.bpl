// Dafny prelude - FRAGMENT
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

const $$Language$Dafny: bool;  // To be recognizable to the ModelViewer as
axiom $$Language$Dafny;        // coming from a Dafny program.

// ---------------------------------------------------------------
// -- Types ---------------------------------------------------{{{
// ---------------------------------------------------------------

type Ty;
type Bv0 = int;

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
axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );

// Specialize Lit to concrete types.
// These aren't logically required, but on some examples improve
// verification speed
function {:identity} LitInt(x: int): int { x }
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

axiom (forall<T> x : T :: { $Box(x) } $Unbox($Box(x)) == x);

axiom (forall bx : Box ::
    { $IsBox(bx, TInt) }
    ( $IsBox(bx, TInt) ==> $Box($Unbox(bx) : int) == bx && $Is($Unbox(bx) : int, TInt)));
axiom (forall bx : Box ::
    { $IsBox(bx, TBool) }
    ( $IsBox(bx, TBool) ==> $Box($Unbox(bx) : bool) == bx && $Is($Unbox(bx) : bool, TBool)));

axiom (forall<T> v : T, t : Ty ::
    { $IsBox($Box(v), t) }
    ( $IsBox($Box(v), t) <==> $Is(v,t) ));
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

axiom(forall v : int  :: { $Is(v,TInt) }  $Is(v,TInt));
axiom(forall v : bool :: { $Is(v,TBool) } $Is(v,TBool));

axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TInt,h) }  $IsAlloc(v,TInt,h));
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

type ORDINAL = Box;  // :| There are more big ordinals than boxes

function ORD#IsNat(ORDINAL): bool;
function ORD#Offset(ORDINAL): int;

function {:inline} ORD#IsLimit(o: ORDINAL): bool { ORD#Offset(o) == 0 }
function {:inline} ORD#IsSucc(o: ORDINAL): bool { 0 < ORD#Offset(o) }

// }}}------------------------------------------------------------
// -- Axiom contexts ------------------------------------------{{{
// ---------------------------------------------------------------

// used to make sure function axioms are not used while their consistency is being checked
const $ModuleContextHeight: int;
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
axiom (forall<T> cl : ClassName, nm: NameFamily ::
   {FieldOfDecl(cl, nm): Field T}
   DeclType(FieldOfDecl(cl, nm): Field T) == cl && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

function $IsGhostField<T>(Field T): bool;

// }}}------------------------------------------------------------
// -- Allocatedness and Heap Succession -----------------------{{{
// ---------------------------------------------------------------


// $IsAlloc and $IsAllocBox are monotonic

axiom(forall<T> h, k : Heap, v : T, t : Ty ::
  { $HeapSucc(h, k), $IsAlloc(v, t, h) }
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));
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
axiom $IsGoodHeap($OneHeap);

function $HeapSucc(Heap, Heap): bool;
axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: { update(h, r, f, x) }
  $IsGoodHeap(update(h, r, f, x)) ==>
  $HeapSucc(h, update(h, r, f, x)));
axiom (forall a,b,c: Heap :: { $HeapSucc(a,b), $HeapSucc(b,c) }
  a != c ==> $HeapSucc(a,b) && $HeapSucc(b,c) ==> $HeapSucc(a,c));
axiom (forall h: Heap, k: Heap :: { $HeapSucc(h,k) }
  $HeapSucc(h,k) ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

// }}}------------------------------------------------------------
// -- Non-determinism -----------------------------------------{{{
// ---------------------------------------------------------------

type TickType;
var $Tick: TickType;

// }}}------------------------------------------------------------
// -- Useful macros -------------------------------------------{{{
// ---------------------------------------------------------------

// havoc everything in $Heap, except {this}+rds+nw
procedure $YieldHavoc(this: ref, rds: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
            $o == this || rds[$Box($o)] || nw[$Box($o)] ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc everything in $Heap, except rds-modi-{this}
procedure $IterHavoc0(this: ref, rds: Set Box, modi: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
            rds[$Box($o)] && !modi[$Box($o)] && $o != this ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);

// havoc $Heap at {this}+modi+nw
procedure $IterHavoc1(this: ref, modi: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
            $o != null && read(old($Heap), $o, alloc) ==>
              read($Heap, $o, $f) == read(old($Heap), $o, $f) ||
              $o == this || modi[$Box($o)] || nw[$Box($o)]);
  ensures $HeapSucc(old($Heap), $Heap);

procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set Box))
                        returns (s: Set Box);
  ensures (forall bx: Box :: { s[bx] } s[bx] <==>
              read(newHeap, this, NW)[bx] ||
              ($Unbox(bx) != null && !read(prevHeap, $Unbox(bx):ref, alloc) && read(newHeap, $Unbox(bx):ref, alloc)));

// }}}------------------------------------------------------------
// -- Axiomatizations -----------------------------------------{{{
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// -- Axiomatization of sets ----------------------------------{{{
// ---------------------------------------------------------------

type Set T = [T]bool;

function Set#Empty<T>(): Set T;
function Set#Equal<T>(Set T, Set T): bool;
// }}}------------------------------------------------------------
// -- Axiomatization of isets ---------------------------------{{{
// ---------------------------------------------------------------

type ISet T = [T]bool;

// }}}------------------------------------------------------------
// -- Axiomatization of multisets -----------------------------{{{
// ---------------------------------------------------------------

type MultiSet T = [T]int;

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

function INTERNAL_add_boogie(x:int, y:int) : int { x + y }
function INTERNAL_sub_boogie(x:int, y:int) : int { x - y }
function INTERNAL_mul_boogie(x:int, y:int) : int { x * y }
function INTERNAL_div_boogie(x:int, y:int) : int { x div y }
function INTERNAL_mod_boogie(x:int, y:int) : int { x mod y }
function {:never_pattern true} INTERNAL_lt_boogie(x:int, y:int) : bool { x < y }
function {:never_pattern true} INTERNAL_le_boogie(x:int, y:int) : bool { x <= y }
function {:never_pattern true} INTERNAL_gt_boogie(x:int, y:int) : bool { x > y }
function {:never_pattern true} INTERNAL_ge_boogie(x:int, y:int) : bool { x >= y }

function Mul(x, y: int): int { x * y }
function Div(x, y: int): int { x div y }
function Mod(x, y: int): int { x mod y }
function Add(x, y: int): int { x + y }
function Sub(x, y: int): int { x - y }

#if ARITH_DISTR
axiom (forall x, y, z: int ::
  { Mul(Add(x, y), z) }
  Mul(Add(x, y), z) == Add(Mul(x, z), Mul(y, z)));
axiom (forall x,y,z: int ::
  { Mul(x, Add(y, z)) }
  Mul(x, Add(y, z)) == Add(Mul(x, y), Mul(x, z)));
//axiom (forall x, y, z: int ::
//  { Mul(Sub(x, y), z) }
//  Mul(Sub(x, y), z) == Sub(Mul(x, z), Mul(y, z)));
#endif
#if ARITH_MUL_DIV_MOD
axiom (forall x, y: int ::
  { Div(x, y), Mod(x, y) }
  { Mul(Div(x, y), y) }
  y != 0 ==>
  Mul(Div(x, y), y) + Mod(x, y) == x);
#endif
#if ARITH_MUL_SIGN
axiom (forall x, y: int ::
  { Mul(x, y) }
  ((0 <= x && 0 <= y) || (x <= 0 && y <= 0) ==> 0 <= Mul(x, y)));
#endif
#if ARITH_MUL_COMM
axiom (forall x, y: int ::
  { Mul(x, y) }
  Mul(x, y) == Mul(y, x));
#endif
#if ARITH_MUL_ASSOC
axiom (forall x, y, z: int ::
  { Mul(x, Mul(y, z)) }
  Mul(y, z) != 0 ==> Mul(x, Mul(y, z)) == Mul(Mul(x, y), z));
#endif

// }}}----------------------------------------------------------------------
