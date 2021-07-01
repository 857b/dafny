namespace Microsoft.Dafny
{
  using System;
  using System.IO;
  using System.Linq;
  using System.Numerics;
  using System.Collections.Generic;
  using System.Diagnostics.Contracts;
  using Microsoft.BaseTypes;
  using Dfy = Microsoft.Dafny;
  using Bpl = Microsoft.Boogie;

  public class DafnyExporter
  {
    protected IdGenerator id_gen;

    public DafnyExporter()
    {
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

    public Edeclarations Export(Program p)
    {
      Contract.Requires(p != null);

      List<ModuleDefinition> mods = p.RawModules().ToList();
      Edeclarations decls = new Edeclarations {
        Method = null,
        Class  = new List<(int, (int, List<(int, Etype)>))> ()
      };

      foreach (ModuleDefinition m in mods) {
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          if (d.GetType() == typeof(DefaultClassDecl)) {
            if (decls.Method != null)
              throw new ExportException("multiple _default class");
            decls.Class.Add((d.ExportUniqueId(id_gen),
                                (0, new List<(int, Etype)>())));
            decls.Method = ExportDefaultClass((DefaultClassDecl)d);

          } else if (d.GetType() == typeof(ClassDecl))
            decls.Class.Add(
                (d.ExportUniqueId(id_gen), ExportClass((ClassDecl)d)));

          else
            throw ExportException.NImpType("TopLevelDecl", d);
        }
      }

      if (decls.Method == null)
        decls.Method = new List<(int, Emethod)> ();

      return decls;
    }

    private List<(int, Emethod)> ExportDefaultClass(DefaultClassDecl c) {
      if (c.TypeArgs.Count != 0)
        throw new ExportException("DefaultClassDecl has some TypeArgs");
      List<(int, Emethod)> methods = new List<(int, Emethod)>();
      foreach (MemberDecl member in c.Members) {
        if (member.GetType() == typeof(Method))
          methods.Add(
              (member.ExportUniqueId(id_gen), ExportMethod((Method)member)));
        else
          throw ExportException.NImpType("DefaultClassDecl::MemberDecl", member);
      }
      return methods;
    }

    private (int, List<(int, Etype)>) ExportClass(ClassDecl c) {
      List<(int, Etype)> fields = new List<(int, Etype)>();
      if (c.TypeArgs.Count != 0)
        throw new ExportException("ClassDecl has some TypeArgs");

      foreach (MemberDecl member in c.Members) {
        if (member.GetType() == typeof(Field)) {
          Field f = (Field)member;
          if (f.HasStaticKeyword || !f.IsMutable || !f.IsUserMutable)
            throw new ExportException("field mutator");
          fields.Add((f.ExportUniqueId(id_gen), ExportType(f.Type)));
        } else
          throw ExportException.NImpType("ClassDecl::MemberDecl", member);
      }

      return (0, fields);
    }

    private Emethod ExportMethod(Method m)
    {
      Emethod method = new Emethod {
        TypeParams = 0,
	    Ins  = new List<(int, Etype)>(),
	    Outs = new List<(int, Etype)>(),
	    Req  = new List<Eexpr>(),
	    Ens  = new List<Eexpr>(),
	    Mod  = new Eframe(),
	    Impl = null
      };
      if (m.TypeArgs.Count != 0)
        throw new ExportException("Method has some TypeArgs");
      foreach (Formal in_f in m.Ins) {
        if (in_f.GetType() != typeof(Formal))
          throw ExportException.NImpType("In", in_f);
        method.Ins.Add((in_f.ExportUniqueId(id_gen), ExportType(in_f.Type)));
      }
      foreach (Formal out_f in m.Outs) {
        if (out_f.GetType() != typeof(Formal))
          throw ExportException.NImpType("Out", out_f);
        method.Outs.Add((out_f.ExportUniqueId(id_gen), ExportType(out_f.Type)));
      }
      foreach (AttributedExpression e in m.Req)
        method.Req.Add(ExportExpr(e.E));
      foreach (AttributedExpression e in m.Ens)
        method.Ens.Add(ExportExpr(e.E));
      foreach (FrameExpression fe in m.Mod.Expressions) {
        if (fe.E.Type.GetType() == typeof(UserDefinedType)) {
          UserDefinedType udt = (UserDefinedType)fe.E.Type;
          if (udt.ResolvedClass == null)
            throw new ExportException("FrameExpression::UserDefinedType ResolvedClass=null");
          else
            method.Mod.Add(ExportExpr(fe.E));
        } else
          throw ExportException.NImpType("FrameExpression", fe.E);
      }
      //TODO +Decreases
      if (m.Body != null)
        method.Impl = ExportStmt(m.Body);

      return method;
    }

    private int GetResolvedClassId(TopLevelDecl ty, bool allowNonNull=false)
    {
      if (ty == null)
        throw new ExportException("GetResolvedClassId of null");
      else if (ty.GetType() == typeof(ClassDecl))
        return ty.ExportUniqueId(id_gen);
      else if (allowNonNull && ty.GetType() == typeof(NonNullTypeDecl))
        return GetResolvedClassId(((NonNullTypeDecl)ty).Class);
      else
        throw ExportException.NImpType("ResolvedClass", ty);
    }

    private int GetUserDefinedTypeClassId(UserDefinedType udt, bool allowNonNull=false)
    {
      return GetResolvedClassId(udt.ResolvedClass, allowNonNull);
    }

    private Etype ExportType(Dfy.Type ty)
    {
      if (ty.TypeArgs.Count != 0)
         throw new ExportException("#TypeArgs != 0");

      if (ty.GetType() == typeof(BoolType))
        return Etype.TBool;
      else if (ty.GetType() == typeof(IntType))
        return Etype.TInt;
      else if (ty.GetType() == typeof(UserDefinedType))
        return new ETCon {
          BaseTy   = new ETref { Tref = new ETClass {
            ClassIdent = GetUserDefinedTypeClassId((UserDefinedType)ty) } },
          ParamsTy = new List<Etype>()
        };
      else
        throw ExportException.NImpType("Type", ty);
    }

    private Estmt ExportStmt(Statement stmt)
    {
      if (stmt.GetType() == typeof(BlockStmt)) {
        return ExportBlockStmt((BlockStmt)stmt);

      } else if (stmt.GetType() == typeof(VarDeclStmt)) {
        VarDeclStmt decl = (VarDeclStmt)stmt;
        if (decl.Update != null)
          throw new ExportException("VarDeclStmt::Update");
        EVarDecl edecl = new EVarDecl { Decls = new List<(int, Etype)>() };
        foreach (LocalVariable lv in decl.Locals) {
          if (lv.GetType() != typeof(LocalVariable))
            throw ExportException.NImpType("LocalVariable", lv);
          edecl.Decls.Add((lv.ExportUniqueId(id_gen), ExportType(lv.Type)));
        }
        return edecl;

      } else if (stmt.GetType() == typeof(AssertStmt)) {
        AssertStmt astmt = (AssertStmt)stmt;
        if (astmt.Proof != null)
          throw new ExportException("AssignStmt::Proof");
        return new EAssert { Guard = ExportExpr(astmt.Expr) };

      } else if (stmt.GetType() == typeof(AssumeStmt)) {
        AssumeStmt astmt = (AssumeStmt)stmt;
        return new EAssume { Guard = ExportExpr(astmt.Expr) };

      } else if (stmt.GetType() == typeof(UpdateStmt)) {
        UpdateStmt update = (UpdateStmt)stmt;
        var res = update.ResolvedStatements;
        if (res.Count == 1){
          if (res[0].GetType() == typeof(AssignStmt)) {
            return ExportAssignStmt((AssignStmt)res[0]);
          } else if (res[0].GetType() == typeof(CallStmt)) {
            return ExportCallStmt((CallStmt)res[0]);
          } else
            throw ExportException.NImpType("UpdateStmt", res[0]);
        } else
          throw new ExportException("UpdateStmt count=" + res.Count);

      } else if (stmt.GetType() == typeof(AssignStmt)) {
        return ExportAssignStmt((AssignStmt)stmt);

      } else if (stmt.GetType() == typeof(IfStmt)) {
        IfStmt ifst = (IfStmt)stmt;
        if (ifst.IsBindingGuard)
          throw new ExportException("IfStmt::BindingGuard");
        return new EIf {
          Guard = ExportExpr(ifst.Guard),
          Thn   = ExportStmtAsBlock(ifst.Thn),
          Els   = ExportStmtAsBlock(ifst.Els)
        };

      } else if (stmt.GetType() == typeof(CallStmt)) {
          return ExportCallStmt((CallStmt)stmt);

      } else
        throw ExportException.NImpType("Statement", stmt);
    }

    private EBlock ExportStmtAsBlock(Statement stmt)
    {
      return ExportBlockStmt(
          stmt == null
          ? new BlockStmt(Bpl.Token.NoToken, Bpl.Token.NoToken,
                          new List<Statement>())
          : stmt.GetType() == typeof(BlockStmt)
          ? (BlockStmt)stmt
          : new BlockStmt(Bpl.Token.NoToken, Bpl.Token.NoToken,
                          new List<Statement>{stmt}));
    }

    private EBlock ExportBlockStmt(BlockStmt b)
    {
      EBlock eb = new EBlock { Stmts = new List<Estmt>() };
      foreach (Statement s in b.Body)
        eb.Stmts.Add(ExportStmt(s));
      return eb;
    }

    private Estmt ExportAssignStmt(AssignStmt s)
    {
      if (s.Rhs.GetType() == typeof(ExprRhs)) {
        // lhs = rhs;
        return new EUpdate {
          Lhss = new List<Eexpr>{ExportExpr(s.Lhs)},
          Rhss = new List<Eexpr>{ExportExpr(((ExprRhs)s.Rhs).Expr)}
        };
      } else if (s.Rhs.GetType() == typeof(TypeRhs)) {
        TypeRhs tyRhs = (TypeRhs)s.Rhs;
        if (tyRhs.ArrayDimensions == null && tyRhs.Arguments == null) {
          // lhs = new C;
          if (tyRhs.EType.TypeArgs.Count != 0)
            throw new ExportException("TypeArgs");
          if (tyRhs.EType.GetType() != typeof(UserDefinedType))
            throw ExportException.NImpType("AssignRhs::new", tyRhs.EType);
          return new ENew {
            Lhs        = ExportExpr(s.Lhs),
            ClassIdent = GetUserDefinedTypeClassId((UserDefinedType)tyRhs.EType, true),
            ParamsTy   = new List<Etype> ()
          };
        } else
          throw new ExportException("AssignRhs::new kind");
      } else
        throw ExportException.NImpType("AssignRhs", s.Rhs);
    }

    private ECall ExportCallStmt(CallStmt clst)
    {
        if (clst.Receiver != null
            && clst.Receiver.GetType() != typeof(StaticReceiverExpr))
          throw ExportException.NImpType("Call Receiver", clst.Receiver);
        return new ECall {
          Lhss        = ExportExprList(clst.Lhs),
          MethodIdent = clst.Method.ExportUniqueId(id_gen),
          ParamsTy    = new List<Etype>(),
          Rhss        = ExportExprList(clst.Args)
        };
    }

    private Eexpr ExportExpr(Expression e)
    {
      if (e is ConcreteSyntaxExpression) {
        return ExportExpr(((ConcreteSyntaxExpression)e).ResolvedExpression);
      } else {

      if (e.GetType() == typeof(LiteralExpr)) {
        LiteralExpr le = (LiteralExpr)e;
        if (le.Value == null)
          return new ELiteral { Lit = new ELitNull() };
        else if (le.Value is bool b)
          return new ELiteral { Lit = new ELitBool { B = b } };
        else if (le.Type.IsIntegerType) {
          if (le.Value is BigInteger i)
            return new ELiteral { Lit = new ELitInt { I = i } };
          else
            throw ExportException.NImpType("LitInt", le.Value);
        } else
          throw ExportException.NImpType("Literal", le.Value);

      } else if (e.GetType() == typeof(IdentifierExpr)) {
        IdentifierExpr id = (IdentifierExpr)e;
        return new EVar { VarId = id.Var.ExportUniqueId(id_gen) };

      } else if (e.GetType() == typeof(UnaryOpExpr)) {
        UnaryOpExpr uop = (UnaryOpExpr)e;
        return new EUnaryOp {
          Op = uop.Op,
          Expr = ExportExpr(uop.E)
        };

      } else if (e.GetType() == typeof(BinaryExpr)) {
        BinaryExpr bop = (BinaryExpr)e;
        return new EBinaryOp {
          Op    = bop.ResolvedOp,
          Expr0 = ExportExpr(bop.E0), Expr1 = ExportExpr(bop.E1)
        };

      } else if (e.GetType() == typeof(MemberSelectExpr)) {
        MemberSelectExpr mse = (MemberSelectExpr)e;
        ExportExpr(mse.Obj);
        if (mse.Member.GetType() == typeof(Field)) {
          return new EMembrSel {
            Obj   = ExportExpr(mse.Obj),
            Field = mse.Member.ExportUniqueId(id_gen)
          };
        } else
          throw ExportException.NImpType("MembrSel", mse.Member);

      } else
        throw ExportException.NImpType("Expression", e);
      }
    }

    private List<Eexpr> ExportExprList(IEnumerable<Expression> es) {
      List<Eexpr> rt = new List<Eexpr>();
      foreach (Expression e in es)
        rt.Add(ExportExpr(e));
      return rt;
    }
  }
}
