using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Dafny;
using Microsoft.BaseTypes;
using Dfy = Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

public class DafnyExporter
{
  public class IdGenerator
  {
    public const int None = -1;
    protected int NextId;

    public IdGenerator()
    {
      NextId = 0;
    }

    public int MakeId(ref int id)
    {
      if (id < 0) {
        id = NextId++;
      }
      return id;
    }
  }

  protected TextWriter  wr;
  protected IdGenerator id_gen;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(wr!=null);
  }

  public DafnyExporter(string filename)
  {
    Contract.Requires(filename != null);
    if (filename == "-") {
      wr = System.Console.Out;
    } else {
      wr = new System.IO.StreamWriter(filename);
    }
    id_gen = new IdGenerator();
  }
  [Serializable]
  public class ExportException : Exception
  {
    public ExportException(string message) : base(message) { }
    static public ExportException NImpType(string loc, Object actual)
    {
      return new ExportException(loc+": "+actual.GetType().Name);
    }
  }

  public void Export(Program p)
  {
    Contract.Requires(p != null);

    List<ModuleDefinition> mods = p.RawModules().ToList();

    foreach (ModuleDefinition m in mods) {
      CommentL("module "+m.Name);

      foreach (TopLevelDecl d in m.TopLevelDecls) {
        if (d.GetType() == typeof(DefaultClassDecl)) {
          ExportDefaultClass((DefaultClassDecl)d);
        } else
          throw ExportException.NImpType("TopLevelDecl", d);
      }
    }
    wr.Flush();
  }

  private void ExportDefaultClass(DefaultClassDecl c) {
    CommentL("_default class");
    foreach (MemberDecl member in c.Members) {
      if (member.GetType() == typeof(Method)) {
        ExportMethod((Method)member);
      } else
        throw ExportException.NImpType("MemberDecl", member);
    }
  }

  private void ExportMethod(Method m)
  {
    wr.WriteLine($"definition method_{m.Name} :: method where");
    wr.WriteLine($"  \"method_{m.Name} == (|");
    wr.Write("  Ins  = [");
    bool sep_wr = false;
    foreach (Formal in_f in m.Ins) {
      if (in_f.GetType() != typeof(Formal))
        throw ExportException.NImpType("In", in_f);
      WriteListSep(ref sep_wr);
      ExportVarDecl(in_f);
    }
    wr.Write("],\n  Outs = [");
    sep_wr = false;
    foreach (Formal out_f in m.Outs) {
      if (out_f.GetType() != typeof(Formal))
        throw ExportException.NImpType("Out", out_f);
      WriteListSep(ref sep_wr);
      ExportVarDecl(out_f);
    }
    wr.Write("],\n  Req  = [");
    sep_wr = false;
    foreach (AttributedExpression e in m.Req) {
      WriteListSep(ref sep_wr);
      ExportExpr(e.E);
    }
    wr.Write("],\n  Ens  = [");
    sep_wr = false;
    foreach (AttributedExpression e in m.Ens) {
      WriteListSep(ref sep_wr);
      ExportExpr(e.E);
    }
    wr.Write("],\n  Body = ");
    //TODO Mod, Decreases
    ExportStmt(m.Body);
    wr.WriteLine("|)\"");
  }

  private void ExportType(Dfy.Type ty)
  {
    if (ty.GetType() == typeof(BoolType)) {
      wr.Write("(tprim TBool)");
    } else if (ty.GetType() == typeof(IntType)) {
      wr.Write("(tprim TInt)");
    } else
      throw ExportException.NImpType("Type", ty);
  }

  private void ExportStmt(Statement stmt)
  {
    if (stmt.GetType() == typeof(BlockStmt)) {
      ExportBlockStmt((BlockStmt)stmt);
    } else if (stmt.GetType() == typeof(VarDeclStmt)) {
      VarDeclStmt decl = (VarDeclStmt)stmt;
      if (decl.Update != null)
        throw new ExportException("VarDeclStmt::Update");
    } else if (stmt.GetType() == typeof(AssertStmt)) {
      AssertStmt astmt = (AssertStmt)stmt;
      if (astmt.Proof != null)
        throw new ExportException("AssignStmt::Proof");
      wr.Write("Assert ");
      ExportExpr(astmt.Expr);
      wr.WriteLine();
    } else if (stmt.GetType() == typeof(UpdateStmt)) {
      UpdateStmt update = (UpdateStmt)stmt;
      var res = update.ResolvedStatements;
      if (res.Count == 1){
        if (res[0].GetType() == typeof(AssignStmt)) {
          ExportAssignStmt((AssignStmt)res[0]);
        } else
          throw ExportException.NImpType("UpdateStmt", res[0]);
      } else
        throw new ExportException("UpdateStmt count=" + res.Count);
    } else if (stmt.GetType() == typeof(AssignStmt)) {
      ExportAssignStmt((AssignStmt)stmt);
    } else if (stmt.GetType() == typeof(IfStmt)) {
      IfStmt ifst = (IfStmt)stmt;
      if (ifst.IsBindingGuard)
        throw new ExportException("IfStmt::BindingGuard");
      wr.Write("If ");
      ExportExpr(ifst.Guard);
      wr.WriteLine();
      ExportStmtAsBlock(ifst.Thn);
      ExportStmtAsBlock(ifst.Els);
    } else
      throw ExportException.NImpType("Statement", stmt);
  }

  private void ExportStmtAsBlock(Statement stmt)
  {
    ExportBlockStmt(
        stmt == null
        ? new BlockStmt(Bpl.Token.NoToken, Bpl.Token.NoToken,
                        new List<Statement>())
        : stmt.GetType() == typeof(BlockStmt)
        ? (BlockStmt)stmt
        : new BlockStmt(Bpl.Token.NoToken, Bpl.Token.NoToken,
                        new List<Statement>{stmt}));
  }

  private void ExportBlockStmt(BlockStmt b)
  {
    wr.Write("(Block [");
    bool sep_wr = false;
    foreach (Statement s in b.Body) {
      if (s.GetType() == typeof(VarDeclStmt)) {
        VarDeclStmt decl = (VarDeclStmt)s;
        foreach (LocalVariable lv in decl.Locals) {
          if (lv.GetType() != typeof(LocalVariable))
            throw ExportException.NImpType("LocalVariable", lv);
          WriteListSep(ref sep_wr);
          ExportVarDecl(lv);
          wr.Write(" ");
        }
      }
    }
    wr.WriteLine("]\n[");
    sep_wr = false;
    foreach (Statement s in b.Body) {
      WriteListSep(ref sep_wr);
      ExportStmt(s);
    }
    wr.WriteLine("])");
  }

  private void ExportAssignStmt(AssignStmt s)
  {
    wr.Write("Update ");
    ExportExpr(s.Lhs);
    wr.Write(" ");
    if (s.Rhs.GetType() == typeof(ExprRhs)) {
      ExportExpr(((ExprRhs)s.Rhs).Expr);
    } else
      throw ExportException.NImpType("AssignRhs", s.Rhs);
    wr.WriteLine();
  }

  private void ExportExpr(Expression e)
  {
    if (e is ConcreteSyntaxExpression) {
      ExportExpr(((ConcreteSyntaxExpression)e).ResolvedExpression);
    } else {

    wr.Write("(");
    if (e.GetType() == typeof(LiteralExpr)) {
      LiteralExpr le = (LiteralExpr)e;
      if (le.Value == null) {
        throw new ExportException("null not implemented");
      } else if (le.Value is bool b) {
        wr.Write($"lit_bool {b}");
      } else if (le.Type.IsIntegerType) {
        if (le.Value is BigDec d) {
          wr.Write($"lit_int {d}");
        } else if (le.Value is BigInteger i) {
          wr.Write($"lit_int {i}");
        } else
          throw ExportException.NImpType("LitInt", le.Value);
      } else
        throw ExportException.NImpType("Literal", le.Value);

    } else if (e.GetType() == typeof(IdentifierExpr)) {
      IdentifierExpr id = (IdentifierExpr)e;
      wr.Write($"Var {id.Var.ExportUniqueId(id_gen)}");

    } else if (e.GetType() == typeof(UnaryOpExpr)) {
      UnaryOpExpr uop = (UnaryOpExpr)e;
      wr.Write("UnaryOp ");
      if (uop.Op == UnaryOpExpr.Opcode.Not) {
        if (uop.E.Type.IsBoolType) {
          wr.Write("Not ");
        } else if (uop.E.Type.IsIntegerType) {
          wr.Write("Neg ");
        } else
          throw new ExportException("Unary Not on type " + uop.E.Type);
      } else
        throw new ExportException("Unary Opcode");
      ExportExpr(uop.E);

    } else if (e.GetType() == typeof(BinaryExpr)) {
      BinaryExpr bop = (BinaryExpr)e;
      wr.Write($"BinaryOp {BinOpName(bop.ResolvedOp)} ");
      ExportExpr(bop.E0);
      wr.Write(" ");
      ExportExpr(bop.E1);

    } else
      throw ExportException.NImpType("Expression", e);
    wr.Write(")");
    }
  }

  static private string BinOpName(BinaryExpr.ResolvedOpcode op)
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
        throw new ExportException("Binary Opcode");
    }
  }

  private void ExportVarDecl(IVariable v)
  {
    wr.Write($"({v.ExportUniqueId(id_gen)}, ");
    ExportType(v.Type);
    wr.Write(")");
  }

  private void CommentL(string c)
  {
    wr.WriteLine("(* " + c + " *)");
  }

  private void Comment(string c)
  {
    wr.Write("(* " + c + " *)");
  }

  private void WriteListSep(ref bool w)
  {
    if (w)
      wr.Write(", ");
    else
      w = true;
  }
}
