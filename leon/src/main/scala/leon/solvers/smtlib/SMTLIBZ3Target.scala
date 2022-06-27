/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Types._

import _root_.smtlib.common._
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Let => SMTLet, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories._

trait SMTLIBZ3Target extends SMTLIBTarget {

  def targetName = "z3"

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-in",
      "-smt2"
    )
  }

  def getNewInterpreter(ctx: LeonContext) = {
    val opts = interpreterOps(ctx)
    context.reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))

    new Z3Interpreter("z3", opts.toArray)
  }

  protected val extSym = SSymbol("_")

  protected var setSort: Option[SSymbol] = None

  override protected def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case SetType(base) =>
          super.declareSort(BooleanType)
          declareSetSort(base)
        case BagType(base) =>
          declareSort(RawArrayType(base, IntegerType))
        case _ =>
          super.declareSort(t)
      }
    }
  }

  protected def declareSetSort(of: TypeTree): Sort = {
    setSort match {
      case None =>
        val s = SSymbol("Set")
        val t = SSymbol("T")
        setSort = Some(s)

        val arraySort = Sort(SMTIdentifier(SSymbol("Array")),
                             Seq(Sort(SMTIdentifier(t)), BoolSort()))

        val cmd = DefineSort(s, Seq(t), arraySort)
        emit(cmd)

      case _ =>
    }

    Sort(SMTIdentifier(setSort.get), Seq(declareSort(of)))
  }

  override protected def fromSMT(t: Term, otpe: Option[TypeTree] = None)
                                (implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    (t, otpe) match {
      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe)) =>
        if (letDefs contains k) {
          // Need to recover value form function model
          fromRawArray(extractRawArray(letDefs(k), tpe), tpe)
        } else {
          throw LeonFatalError("Array on non-function or unknown symbol "+k)
        }

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), Some(tpe)) =>
        val ktpe = sorts.fromB(k)
        val vtpe = sorts.fromB(v)

        fromRawArray(RawArrayValue(ktpe, Map(), fromSMT(defV, vtpe)), tpe)

      case _ =>
        super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, base) =>
      declareSort(fs.getType)

      toSMT(RawArrayValue(base, elems.map {
        case k => k -> BooleanLiteral(true)
      }.toMap, BooleanLiteral(false)))

    case SubsetOf(ss, s) =>
      // a isSubset b   ==>   (a zip b).map(implies) == (* => true)
      val allTrue = ArrayConst(declareSort(s.getType), True())

      SMTEquals(ArrayMap(SSymbol("implies"), toSMT(ss), toSMT(s)), allTrue)

    case SetAdd(s, e) =>
      ArraysEx.Store(toSMT(s), toSMT(e), True())

    case ElementOfSet(e, s) =>
      ArraysEx.Select(toSMT(s), toSMT(e))

    case SetDifference(a, b) =>
      // a -- b
      // becomes:
      // a && not(b)

      ArrayMap(SSymbol("and"), toSMT(a), ArrayMap(SSymbol("not"), toSMT(b)))

    case SetUnion(l, r) =>
      ArrayMap(SSymbol("or"), toSMT(l), toSMT(r))

    case SetIntersection(l, r) =>
      ArrayMap(SSymbol("and"), toSMT(l), toSMT(r))

    case fb @ FiniteBag(elems, base) =>
      declareSort(fb.getType)

      toSMT(RawArrayValue(base, elems, InfiniteIntegerLiteral(0)))

    case BagAdd(b, e) =>
      val bid = FreshIdentifier("b", b.getType, true)
      val eid = FreshIdentifier("e", e.getType, true)
      val (bSym, eSym) = (id2sym(bid), id2sym(eid))
      SMTLet(VarBinding(bSym, toSMT(b)), Seq(VarBinding(eSym, toSMT(e))), ArraysEx.Store(bSym, eSym,
        Ints.Add(ArraysEx.Select(bSym, eSym), Ints.NumeralLit(1))))

    case MultiplicityInBag(e, b) =>
      ArraysEx.Select(toSMT(b), toSMT(e))

    case BagUnion(b1, b2) =>
      val plus = SortedSymbol("+", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))
      ArrayMap(plus, toSMT(b1), toSMT(b2))

    case BagIntersection(b1, b2) =>
      toSMT(BagDifference(b1, BagDifference(b1, b2)))

    case BagDifference(b1, b2) =>
      val abs   = SortedSymbol("abs", List(IntegerType).map(declareSort), declareSort(IntegerType))
      val plus  = SortedSymbol("+", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))
      val minus = SortedSymbol("-", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))
      val div   = SortedSymbol("/", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))

      val did = FreshIdentifier("d", b1.getType, true)
      val dSym = id2sym(did)

      val all2 = ArrayConst(declareSort(IntegerType), Ints.NumeralLit(2))

      SMTLet(VarBinding(dSym, ArrayMap(minus, toSMT(b1), toSMT(b2))), Seq(),
        ArrayMap(div, ArrayMap(plus, dSym, ArrayMap(abs, dSym)), all2))

    case _ =>
      super.toSMT(e)
  }

  protected def extractRawArray(s: DefineFun, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): RawArrayValue = s match {
    case DefineFun(SMTFunDef(a, Seq(SortedVar(arg, akind)), rkind, body)) =>
      val (argTpe, retTpe) = tpe match {
        case SetType(base) => (base, BooleanType)
        case MapType(from, to) => (from, library.optionType(to))
        case ArrayType(base) => (Int32Type, base)
        case FunctionType(args, ret) => (tupleTypeWrap(args), ret)
        case RawArrayType(from, to) => (from, to)
        case _ => unsupported(tpe, "Unsupported type for (un)packing into raw arrays (got kinds "+akind+" -> "+rkind+")")
      }

      def extractCases(e: Term): (Map[Expr, Expr], Expr) = e match {
        case ITE(SMTEquals(SimpleSymbol(`arg`), k), v, e) =>
          val (cs, d) = extractCases(e)
          (Map(fromSMT(k, argTpe) -> fromSMT(v, retTpe)) ++ cs, d)
        case e =>
          (Map(),fromSMT(e, retTpe))
      }

      val (cases, default) = extractCases(body)

      RawArrayValue(argTpe, cases, default)

    case _ =>
      throw LeonFatalError("Unable to extract "+s)
  }

  protected object SortedSymbol {
    def apply(op: String, from: List[Sort], to: Sort) = {
      def simpleSort(s: Sort): Boolean = s.subSorts.isEmpty && !s.id.isIndexed
      assert(from.forall(simpleSort) && simpleSort(to), "SortedSymbol is only defined for simple sorts")
      SList(SSymbol(op), SList(from.map(_.id.symbol): _*), to.id.symbol)
    }
  }

  protected object ArrayMap {
    def apply(op: SExpr, arrs: Term*) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("map"), List(op))),
        arrs
      )
    }
  }

  protected object ArrayConst {
    def apply(sort: Sort, default: Term) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(sort)),
        List(default))
    }
  }
}
