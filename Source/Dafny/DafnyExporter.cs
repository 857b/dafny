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

  const string Lbd_None = "(\\<lambda> _ . None)";

  public void Export(Program p)
  {
    Contract.Requires(p != null);

    List<ModuleDefinition> mods = p.RawModules().ToList();
    List<(int, string)> classes = new List<(int, string)>();
    string methods = null;

    foreach (ModuleDefinition m in mods) {
      CommentL("module "+m.Name);

      foreach (TopLevelDecl d in m.TopLevelDecls) {
        if (d.GetType() == typeof(DefaultClassDecl)) {
          if (methods != null)
            throw new ExportException("multiple _default class");
          methods = ExportDefaultClass((DefaultClassDecl)d);

        } else if (d.GetType() == typeof(ClassDecl)) {
          string decl = ExportClass((ClassDecl)d);
          classes.Add((d.ExportUniqueId(id_gen), decl));

        } else
          throw ExportException.NImpType("TopLevelDecl", d);
      }
    }

    string prog_decl = "program";
    string class_fun = "classes_decl";
    string class_assoc = "classes_assoc";
    ExportAssoc(classes, "class_ident", "(nat \\<times> (cfield_ident => type option))",
                class_assoc, class_fun);

    wr.WriteLine($"definition {prog_decl} :: declarations where");
    wr.WriteLine($"  \"{prog_decl} == (|");
    if (methods != null)
      wr.WriteLine($"    Method = {methods},");
    else
      wr.WriteLine($"    Method = {Lbd_None},");
    wr.WriteLine($"    Class  = {class_fun},");
    wr.WriteLine($"    IndTy  = {Lbd_None}");
    wr.WriteLine("  |)\"");
    wr.Flush();
  }

  /* returns the name of a function "method_ident .> method" */
  private string ExportDefaultClass(DefaultClassDecl c) {
    if (c.TypeArgs.Count != 0)
      throw new ExportException("DefaultClassDecl has some TypeArgs");
    CommentL("_default class");
    List<(int, string)> methods = new List<(int, string)>();
    foreach (MemberDecl member in c.Members) {
      if (member.GetType() == typeof(Method)) {
        string method_decl = ExportMethod((Method)member);
        methods.Add((member.ExportUniqueId(id_gen), method_decl));
      } else
        throw ExportException.NImpType("DefaultClassDecl::MemberDecl", member);
    }
    string methods_fun   = "methods_fun";
    string methods_assoc = "methods_assoc";
    ExportAssoc(methods, "method_ident", "method", methods_assoc, methods_fun);
    return methods_fun;
  }

  /* returns the name of a "(nat <*> (cfield_ident .> type))" */
  private string ExportClass(ClassDecl c) {
    if (c.TypeArgs.Count != 0)
      throw new ExportException("ClassDecl has some TypeArgs");
    CommentL($"class {c}");
    string name = $"class{c.ExportUniqueId(id_gen)}_{c.Name}";

    List<(int, string)> fields = new List<(int, string)>();
    foreach (MemberDecl member in c.Members) {
      if (member.GetType() == typeof(Field)) {
        Field f = (Field)member;
        if (f.HasStaticKeyword || !f.IsMutable || !f.IsUserMutable)
          throw new ExportException("field mutator");
        TextWriter wr_sv = wr;
        StringWriter ty_wr = new StringWriter();
        wr = ty_wr;
        ExportType(f.Type);
        wr = wr_sv;
        fields.Add((f.ExportUniqueId(id_gen), ty_wr.ToString()));

      } else
        throw ExportException.NImpType("ClassDecl::MemberDecl", member);
    }
    string fields_fun   = $"{name}_fields";
    string fields_assoc = $"{name}_assoc";
    ExportAssoc(fields, "cfield_ident", "type", fields_assoc, fields_fun);

    string decl = $"{name}_decl";
    wr.WriteLine($"definition {decl} :: \"nat \\<times> (cfield_ident => type option)\" where");
    wr.WriteLine($"  \"{decl} == ({0}, {fields_fun})\"");
    return decl;
  }

  /* returns the name of a "method" */
  private string ExportMethod(Method m)
  {
    if (m.TypeArgs.Count != 0)
      throw new ExportException("Method has some TypeArgs");
    string name = $"method{m.ExportUniqueId(id_gen)}_{m.Name}";
    wr.WriteLine($"definition {name} :: method where");
    wr.WriteLine($"  \"{name} == (|");
    wr.Write("  Ins  = [");
    bool sep_wr = false;
    foreach (Formal in_f in m.Ins) {
      if (in_f.GetType() != typeof(Formal))
        throw ExportException.NImpType("In", in_f);
      WriteSep(ref sep_wr);
      ExportVarDecl(in_f);
    }
    wr.Write("],\n  Outs = [");
    sep_wr = false;
    foreach (Formal out_f in m.Outs) {
      if (out_f.GetType() != typeof(Formal))
        throw ExportException.NImpType("Out", out_f);
      WriteSep(ref sep_wr);
      ExportVarDecl(out_f);
    }
    wr.Write("],\n  Req  = [");
    sep_wr = false;
    foreach (AttributedExpression e in m.Req) {
      WriteSep(ref sep_wr);
      ExportExpr(e.E);
    }
    wr.Write("],\n  Ens  = [");
    sep_wr = false;
    foreach (AttributedExpression e in m.Ens) {
      WriteSep(ref sep_wr);
      ExportExpr(e.E);
    }
    wr.Write("],\n  Mod  = ");
    bool isUnframed = false;
    foreach (FrameExpression fe in m.Mod.Expressions) {
      if (fe.E is WildcardExpr) {
        isUnframed = true;
        wr.Write("UnFramed");
        break;
      }
    }
    if (!isUnframed) {
      wr.Write("FrameExprs {");
      sep_wr = false;
      foreach (FrameExpression fe in m.Mod.Expressions) {
        if (fe.E.Type.GetType() == typeof(UserDefinedType)) {
          UserDefinedType udt = (UserDefinedType)fe.E.Type;
          if (udt.ResolvedClass == null)
            throw new ExportException("FrameExpression::UserDefinedType ResolvedClass=null");
          else {
            WriteSep(ref sep_wr);
            ExportExpr(fe.E);
          }
        } else
          throw ExportException.NImpType("FrameExpression", fe.E);
      }
      wr.Write("}");
    }
    //TODO +Decreases
    wr.Write(",\n  Body = ");
    if (m.Body == null)
      wr.Write("None");
    else {
      wr.Write("Some (");
      ExportStmt(m.Body);
      wr.Write(")");
    }
    wr.WriteLine("|)\"");

    return name;
  }

  private void ExportType(Dfy.Type ty)
  {
    if (ty.TypeArgs.Count != 0)
       throw new ExportException("#TypeArgs > 0");

    if (ty.GetType() == typeof(BoolType)) {
      wr.Write("(tprim TBool)");
    } else if (ty.GetType() == typeof(IntType)) {
      wr.Write("(tprim TInt)");
    } else if (ty.GetType() == typeof(UserDefinedType)) {
      UserDefinedType udt = (UserDefinedType)ty;
      if (udt.ResolvedClass == null)
        throw new ExportException("Type::UserDefinedType ResolvedClass=null");
      else if (udt.ResolvedClass.GetType() == typeof(ClassDecl))
        wr.Write($"(TCon (tclass {udt.ResolvedClass.ExportUniqueId(id_gen)}) [])");
      else
        throw ExportException.NImpType("Type::UserDefinedType", udt.ResolvedClass);

    } else
      throw ExportException.NImpType("Type", ty);
  }

  private bool ExportStmt(Statement stmt)
  {
    if (stmt.GetType() == typeof(BlockStmt)) {
      ExportBlockStmt((BlockStmt)stmt);

    } else if (stmt.GetType() == typeof(VarDeclStmt)) {
      VarDeclStmt decl = (VarDeclStmt)stmt;
      if (decl.Update != null)
        throw new ExportException("VarDeclStmt::Update");
      return false;

    } else if (stmt.GetType() == typeof(AssertStmt)) {
      AssertStmt astmt = (AssertStmt)stmt;
      if (astmt.Proof != null)
        throw new ExportException("AssignStmt::Proof");
      wr.Write("Assert ");
      ExportExpr(astmt.Expr);
      wr.WriteLine();

    } else if (stmt.GetType() == typeof(AssumeStmt)) {
      AssumeStmt astmt = (AssumeStmt)stmt;
      wr.Write("Assume ");
      ExportExpr(astmt.Expr);
      wr.WriteLine();

    } else if (stmt.GetType() == typeof(UpdateStmt)) {
      UpdateStmt update = (UpdateStmt)stmt;
      var res = update.ResolvedStatements;
      if (res.Count == 1){
        if (res[0].GetType() == typeof(AssignStmt)) {
          ExportAssignStmt((AssignStmt)res[0]);
        } else if (res[0].GetType() == typeof(CallStmt)) {
          ExportCallStmt((CallStmt)res[0]);
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

    } else if (stmt.GetType() == typeof(CallStmt)) {
        ExportCallStmt((CallStmt)stmt);

    } else
      throw ExportException.NImpType("Statement", stmt);
    return true;
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
    wr.Write("(Block {");
    bool sep_wr = false;
    foreach (Statement s in b.Body) {
      if (s.GetType() == typeof(VarDeclStmt)) {
        VarDeclStmt decl = (VarDeclStmt)s;
        foreach (LocalVariable lv in decl.Locals) {
          if (lv.GetType() != typeof(LocalVariable))
            throw ExportException.NImpType("LocalVariable", lv);
          WriteSep(ref sep_wr);
          ExportVarDecl(lv);
          wr.Write(" ");
        }
      }
    }
    wr.WriteLine("}\n[");
    sep_wr = false;
    foreach (Statement s in b.Body) {
      WriteSep(ref sep_wr);
      sep_wr = ExportStmt(s);
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

  private void ExportCallStmt(CallStmt clst)
  {
      if (clst.Receiver != null
          && clst.Receiver.GetType() != typeof(StaticReceiverExpr))
        throw ExportException.NImpType("Call Receiver", clst.Receiver);
      wr.Write("Call ");
      ExportExprList(clst.Lhs);
      wr.Write(" ");
      wr.Write(clst.Method.ExportUniqueId(id_gen));
      wr.Write(" ");
      ExportExprList(clst.Args);
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
        wr.Write("lit_null");
      } else if (le.Value is bool b) {
        wr.Write($"lit_bool {(b?"True":"False")}");
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

    } else if (e.GetType() == typeof(MemberSelectExpr)) {
      MemberSelectExpr mse = (MemberSelectExpr)e;
      wr.Write("MembrSel ");
      ExportExpr(mse.Obj);
      if (mse.Member.GetType() == typeof(Field))
        wr.Write($" {mse.Member.ExportUniqueId(id_gen)}");
      else
        throw ExportException.NImpType("MembrSel", mse.Member);

    } else
      throw ExportException.NImpType("Expression", e);
    wr.Write(")");
    }
  }

  private void ExportExprList(IEnumerable<Expression> es) {
    wr.Write("[");
    bool sep_wr = false;
    foreach (Expression e in es) {
        WriteSep(ref sep_wr);
        ExportExpr(e);
    }
    wr.Write("]");
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

  private void WriteSep(ref bool w, string sep=", ", string els="")
  {
    if (w)
      wr.Write(sep);
    else {
      wr.Write(els);
      w = true;
    }
  }

  private void ExportAssoc(IEnumerable<(int,string)> assoc,
      string key_ty, string val_ty,
      string assoc_name, string fun_name)
  {
    wr.WriteLine($"definition {assoc_name} :: \"({key_ty} \\<times> {val_ty}) list\" where");
    wr.Write($"  \"{assoc_name} == [");
    bool sep_wr = false;
    foreach ((int key, string val) d in assoc) {
      WriteSep(ref sep_wr);
      wr.Write($"({d.key}, {d.val})");
    }
    wr.WriteLine("]\"");
    wr.WriteLine($"definition {fun_name} :: \"{key_ty} => {val_ty} option\" where");
    wr.WriteLine($"  \"{fun_name} == assoc_find {assoc_name}\"");
  }
}
