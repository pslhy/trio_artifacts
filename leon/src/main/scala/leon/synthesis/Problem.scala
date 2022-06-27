/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Path
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.Common._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Definitions.FunDef
import Witnesses._

/** Defines a synthesis triple of the form:
  * ⟦ as ⟨ ws && pc | phi ⟩ xs ⟧
  * 
  * @param as The list of input identifiers so far
  * @param ws The axioms and other already proven theorems
  * @param pc The path condition so far
  * @param phi The formula on `as` and `xs` to satisfy
  * @param xs The list of output identifiers for which we want to compute a function
  * @note Since the examples are not eagerly filtered by [[Rule]]s, some may not
  *       pass the path condition. Use [[qebFiltered]] to get the legal ones.
  */
case class Problem(as: List[Identifier], ws: Expr, pc: Path, phi: Expr, xs: List[Identifier], eb: ExamplesBank = ExamplesBank.empty) extends Printable {

  // require(eb.examples.forall(_.ins.size == as.size))

  val TopLevelAnds(wsList) = ws

  def inType  = tupleTypeWrap(as.map(_.getType))
  def outType = tupleTypeWrap(xs.map(_.getType))

  def allAs = as ++ (pc.bindings.map(_._1) diff wsList.collect{ case Inactive(i) => i })

  def asString(implicit ctx: LeonContext): String = {
    def pad(padding: String, text: String) = text.lines.mkString(s"\n|$padding")
    val pcws = pc withCond ws

    val ebInfo = "/"+eb.valids.size+","+eb.invalids.size+"/"

    val spec = if(!isTestBased) {
      s"φ ${pad("    ", phi.asString)}"
    } else {
      def vsToString(vs: Seq[Expr]): String = {
        if(vs.size == 1) {
          vs.head.asString
        } else {
          vs.map(_.asString).mkString("(", ", ", ")")
        }
      }

      val tests = eb.valids.collect {
        case InOutExample(ins, outs) =>
          vsToString(ins)+" -> "+vsToString(outs)
      }

      s"T $tests"
    }

    s"""|⟦ α ${if (as.nonEmpty) as.map(_.asString).mkString(", ") else "()"}
        |  Π ${pad("    ", pcws.fullClause.asString)}
        |  $spec
        |  x ${if (xs.nonEmpty) xs.map(_.asString).mkString(", ") else "()"}
        |⟧ $ebInfo""".stripMargin
  }

  def withWs(es: Traversable[Expr]) = {
    copy(ws = andJoin(wsList ++ es))
  }

  def qebFiltered(implicit sctx: SearchContext) = qeb.evalAndDiscardIns.filterIns(pc.fullClause)

  // Qualified example bank, allows us to perform operations (e.g. filter) with expressions
  def qeb(implicit sctx: SearchContext) = QualifiedExamplesBank(this.as, this.xs, eb)

  lazy val hasOutputTests = eb.valids.exists{
    case io: InOutExample => true
    case _ => false
  }

  lazy val isTestBased = (phi == BooleanLiteral(true)) && hasOutputTests
}

object Problem {

  def fromSpec(
    spec: Expr,
    pc: Path = Path.empty,
    eb: ExamplesBank = ExamplesBank.empty,
    fd: Option[FunDef] = None
  ): Problem = {
    val xs = (spec match {
      case Lambda(args, _) => args.map(_.id)
      case IsTyped(_, FunctionType(from, to)) =>
        from map (FreshIdentifier("x", _, alwaysShowUniqueID = true))
      case _ =>
        throw LeonFatalError(s"$spec is the spec of a choose but is not a function?")
    }).toList

    val phi = application(simplifyLets(spec), xs map { _.toVariable})
    val as = (variablesOf(phi) ++ pc.variables -- xs).toList.sortBy(_.name)

    val sortedAs = fd match {
      case None => as
      case Some(fd) =>
        val argsIndex = fd.params.map(_.id).zipWithIndex.toMap.withDefaultValue(100)
        as.sortBy(a => argsIndex(a))
    }

    val (pcs, wss) = pc.partition {
      case w: Witness => false
      case _ => true
    }

    Problem(sortedAs, andJoin(wss), pcs, phi, xs, eb)
  }

}
