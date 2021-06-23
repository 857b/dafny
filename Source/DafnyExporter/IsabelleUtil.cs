using System;
using System.Collections.Generic;

namespace Isabelle.Ast {
  interface IToIsaTerm {
    Term ToIsaTerm();
  }

  class IsaUtil {
	public static Term TermS(string id)
	{
	  return new TermIdent(new SimpleIdentifier(id));
    }
    public static Term TermAppS(string fun, params Term[] args)
    {
      return new TermApp(TermS(fun), args);
    }
    public static Term TermListE(IEnumerable<Term> ts)
    {
      return new TermList(new List<Term>(ts));
    }
    public static Term TermRecordP(params (string F,Term V)[] fs)
    {
      var lfs = new List<Tuple<string, Term>>();
      foreach (var t in fs)
        lfs.Add(Tuple.Create(t.F, t.V));
      return new TermRecord(lfs);
    }
  }
}
