using System;
using System.Collections.Generic;
using System.Numerics;
using System.Linq;
using Isa = Isabelle.Ast;
using static Isabelle.Ast.IsaUtil;

namespace Microsoft.Dafny {

#region types
  public enum Eprim_ty { ETInt, ETBool }
  public abstract class Eref_ty : Isa.IToIsaTerm {
	public abstract Isa.Term ToIsaTerm();
  }
  public class ETClass : Eref_ty {
    public int ClassIdent;
	public override Isa.Term ToIsaTerm() {
      return TermAppS("TClass", TermAppS("class_ident",
	           new Isa.NatConst(ClassIdent)));
    }
  }

  public abstract class Ety : Isa.IToIsaTerm {
	public abstract Isa.Term ToIsaTerm();
  }
  public class ETprim : Ety {
    public Eprim_ty Tprim;
	public override Isa.Term ToIsaTerm() {
	  switch (Tprim) {
		case Eprim_ty.ETInt:
		  return TermAppS("Tprim", TermS("TInt"));
		case Eprim_ty.ETBool:
		  return TermAppS("Tprim", TermS("TBool"));
	  }
      throw new DafnyExporter.ExportException("Tprim");
	}
  }
  public class ETref : Ety {
    public Eref_ty Tref;
	public override Isa.Term ToIsaTerm() {
	  return TermAppS("Tref", Tref.ToIsaTerm());
    }
  }

  public abstract class Etype : Isa.IToIsaTerm {
    public static Etype TBool = new ETCon {
      BaseTy   = new ETprim {Tprim = Eprim_ty.ETBool},
      ParamsTy = new List<Etype> () };
	public static Etype TInt  = new ETCon {
      BaseTy   = new ETprim {Tprim = Eprim_ty.ETInt},
      ParamsTy = new List<Etype> () };

	public abstract Isa.Term ToIsaTerm();
  }
  public class ETCon : Etype {
	public Ety BaseTy;
	public List<Etype> ParamsTy;
	public override Isa.Term ToIsaTerm() {
	  return TermAppS("TCon", BaseTy.ToIsaTerm(),
			   TermListE(ParamsTy.Select(t => t.ToIsaTerm())));
	}
  }
#endregion

#region expressions
  public abstract class Eliteral : Isa.IToIsaTerm {
	public abstract Isa.Term ToIsaTerm();
  }
  public class ELitInt : Eliteral {
    public BigInteger I;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("LitInt", new Isa.IntConst(
				 Microsoft.BaseTypes.BigNum.FromBigInt(I)));
    }
  }
  public class ELitBool : Eliteral {
	public bool B;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("LitBool", new Isa.BoolConst(B));
    }
  }
  public class ELitNull : Eliteral {
    public override Isa.Term ToIsaTerm() {
	  return TermS("LitNull");
	}
  }

  public abstract class Eexpr : Isa.IToIsaTerm {
	public abstract Isa.Term ToIsaTerm();
  }
  public class ELiteral : Eexpr {
	public Eliteral Lit;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Literal", Lit.ToIsaTerm());
    }
  }
  public class EVar : Eexpr {
	public int VarId;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Var", TermAppS("var_ident", new Isa.NatConst(VarId)));
    }
  }
  public class EUnaryOp : Eexpr {
	public UnaryOpExpr.Opcode Op;
	public Eexpr Expr;

    public override Isa.Term ToIsaTerm() {
      return TermAppS("UnaryOp", TermS(OpName(Op)), Expr.ToIsaTerm());
    }
    static private string OpName(UnaryOpExpr.Opcode op)
    {
      switch (op) {
        case UnaryOpExpr.Opcode.Not:       return "Not";
        case UnaryOpExpr.Opcode.Allocated: return "Allocated";
        default:
          throw new DafnyExporter.ExportException("Unary Opcode");
      }
    }
  }
  public class EBinaryOp : Eexpr {
    public BinaryExpr.ResolvedOpcode Op;
	public Eexpr Expr0, Expr1;

    public override Isa.Term ToIsaTerm() {
      return TermAppS("BinaryOp", TermS(OpName(Op)),
                        Expr0.ToIsaTerm(), Expr1.ToIsaTerm());
    }
	static private string OpName(BinaryExpr.ResolvedOpcode op)
    {
      switch (op) {
        case BinaryExpr.ResolvedOpcode.And:       return "And";
        case BinaryExpr.ResolvedOpcode.Or:        return "Or";
        case BinaryExpr.ResolvedOpcode.EqCommon:  return "Eq";
        case BinaryExpr.ResolvedOpcode.NeqCommon: return "Neq";
        case BinaryExpr.ResolvedOpcode.Lt:        return "Lt";
        case BinaryExpr.ResolvedOpcode.Le:        return "Le";
        case BinaryExpr.ResolvedOpcode.Ge:        return "Ge";
        case BinaryExpr.ResolvedOpcode.Gt:        return "Gt";
        case BinaryExpr.ResolvedOpcode.Add:       return "Add";
        case BinaryExpr.ResolvedOpcode.Sub:       return "Sub";
        case BinaryExpr.ResolvedOpcode.Mul:       return "Mul";
        case BinaryExpr.ResolvedOpcode.Div:       return "Div";
        default:
          throw new DafnyExporter.ExportException("Binary Opcode");
      }
    }
  }
  public class EMembrSel : Eexpr {
	public Eexpr Obj;
	public int Field;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("MembrSel", Obj.ToIsaTerm(),
                TermAppS("cfield_ident", new Isa.NatConst(Field)));
    }
  }
  public class EOld : Eexpr {
    public Eexpr Expr;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Old", Expr.ToIsaTerm());
    }
  }

  public class Eframe : List<Eexpr>, Isa.IToIsaTerm {
    public Isa.Term ToIsaTerm() {
      return new Isa.TermSet(this.Select(e => e.ToIsaTerm()));
    }
  }

  public abstract class Ewild_frame : Isa.IToIsaTerm {
	public abstract Isa.Term ToIsaTerm();
  }
  public class EFrame : Ewild_frame {
	public Eframe Frame;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Frame", Frame.ToIsaTerm());
    }
  }
  public class EWildFrame : Ewild_frame {
    public override Isa.Term ToIsaTerm() {
      return TermS("WildFrame");
    }
  }
#endregion

#region statements
  public abstract class Estmt : Isa.IToIsaTerm {
	public abstract Isa.Term ToIsaTerm();
  }

  public class EBlock : Estmt {
  	public List<Estmt> Stmts;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Block", TermListE(Stmts.Select(s => s.ToIsaTerm())));
    }
  }
  public class EVarDecl : Estmt {
	public List<(int Id, Etype Ty)> Decls;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("VarDecl", TermAppS("map_of", TermListE(
               Decls.Select(d => new Isa.TermTuple(
                 TermAppS("var_ident", new Isa.NatConst(d.Id)), d.Ty.ToIsaTerm()
          )))));
    }
  }
  public class EUpdate : Estmt {
    public List<Eexpr> Lhss, Rhss;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Update",
          TermListE(Lhss.Select(e => e.ToIsaTerm())),
          TermListE(Rhss.Select(e => e.ToIsaTerm())));
    }
  }
  public class ENew : Estmt {
    public Eexpr Lhs;
	public int ClassIdent;
	public List<Etype> ParamsTy;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("New", Lhs.ToIsaTerm(), TermRecordP(
            ("BaseType", TermAppS("class_ident", new Isa.NatConst(ClassIdent))),
            ("TypeArgs", TermListE(ParamsTy.Select(t => t.ToIsaTerm())))));
    }
  }
  public class EAssert : Estmt {
    public Eexpr Guard;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Assert", Guard.ToIsaTerm());
    }
  }
  public class EAssume : Estmt {
    public Eexpr Guard;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Assume", Guard.ToIsaTerm());
    }
  }
  public class EIf : Estmt {
    public Eexpr Guard;
	public Estmt Thn, Els;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("If", Guard.ToIsaTerm(),
                    Thn.ToIsaTerm(), Els.ToIsaTerm());
    }
  }
  public class EWhile : Estmt {
    public Eexpr Guard;
	public Estmt Body;
	public List<Eexpr> Invariant;
	public Ewild_frame ModFrame;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("While", Guard.ToIsaTerm(), Body.ToIsaTerm(), TermRecordP(
            ("LoopInv", TermListE(Invariant.Select(e => e.ToIsaTerm()))),
            ("Mod", ModFrame.ToIsaTerm())));
    }
  }
  public class EBreak : Estmt {
    public override Isa.Term ToIsaTerm() {
      return TermS("Break");
    }
  }
  public class ECall : Estmt {
    public List<Eexpr> Lhss;
    public int MethodIdent;
    public List<Etype> ParamsTy;
    public List<Eexpr> Rhss;
    public override Isa.Term ToIsaTerm() {
      return TermAppS("Call",
          new Isa.TermList(new List<Isa.Term>(Lhss.Select(e => e.ToIsaTerm()))),
          TermAppS("method_ident", new Isa.NatConst(MethodIdent)),
          new Isa.TermList(new List<Isa.Term>(ParamsTy.Select(t => t.ToIsaTerm()))),
          new Isa.TermList(new List<Isa.Term>(Rhss.Select(e => e.ToIsaTerm()))));
    }
  }
#endregion

  public class Emethod : Isa.IToIsaTerm {
    public int TypeParams;
	public List<(int Id, Etype Ty)> Ins;
	public List<(int Id, Etype Ty)> Outs;
	public List<Eexpr> Req;
	public List<Eexpr> Ens;
	public Eframe Mod;
	public Estmt Impl;

    public Isa.Term ToIsaTerm() {
      return TermRecordP(
        ("TypeParams", (Isa.Term)new Isa.NatConst(TypeParams)),
        ("Ins", TermListE(Ins.Select(d => new Isa.TermTuple(
            TermAppS("var_ident", new Isa.NatConst(d.Id)), d.Ty.ToIsaTerm())))),
        ("Outs", TermListE(Outs.Select(d => new Isa.TermTuple(
            TermAppS("var_ident", new Isa.NatConst(d.Id)), d.Ty.ToIsaTerm())))),
        ("Req", TermListE(Req.Select(e => e.ToIsaTerm()))),
        ("Ens", TermListE(Ens.Select(e => e.ToIsaTerm()))),
        ("Mod", Mod.ToIsaTerm()),
        ("Impl", Impl == null ? TermS("None")
                              : TermAppS("Some", Impl.ToIsaTerm())));
    }
  }

  public class Edeclarations : Isa.IToIsaTerm {
    public List<(int Id, Emethod M)> Method;
	public List<(int Id, (int Nps, List<(int Id, Etype Ty)> Fs) C)> Class;
    public Isa.Term ToIsaTerm() {
      return TermRecordP(
        ("Method", TermAppS("map_of", TermListE(Method.Select(m =>
            new Isa.TermTuple(TermAppS("method_ident", new Isa.NatConst(m.Id)),
                              m.M.ToIsaTerm()))))),
        ("Class", TermAppS("map_of", TermListE(Class.Select(c =>
            new Isa.TermTuple(TermAppS("class_ident", new Isa.NatConst(c.Id)),
              new Isa.TermTuple(new Isa.NatConst(c.C.Nps),
                TermAppS("map_of", TermListE(c.C.Fs.Select(f =>
                   new Isa.TermTuple(
                     TermAppS("cfield_ident", new Isa.NatConst(f.Id)),
                     f.Ty.ToIsaTerm()
            )))))))))),
         ("IndTy", TermS("Map.empty")),
         ("IndCt", TermS("Map.empty")),
         ("cfield_wtype", TermS("Map.empty")/*placeholder*/) );
    }
  }
}
