/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.structure

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.factories._
import invariant.util._
import Util._
import PredicateUtil._
import scala.language.implicitConversions
import ExpressionTransformer._

/**
 * Some utiliy methods for functions.
 * This also does caching to improve performance.
 */
object FunctionUtils {

  //the template function
  val tmplFunctionName = "tmpl"
  /**
   * checks if the function name is 'tmpl' and there is only one argument
   * if not, type checker would anyway throw an error if leon.invariant._ is included
   */
  def isTemplateInvocation(finv: Expr) = {
    finv match {
      case FunctionInvocation(funInv, args) =>
        funInv.id.name == tmplFunctionName && funInv.returnType == BooleanType &&
          args.size == 1 && args(0).isInstanceOf[Lambda]
      case _ =>
        false
    }
  }

  def isQMark(e: Expr) = e match {
    case FunctionInvocation(TypedFunDef(fd, Seq()), args) =>
      fd.id.name == "?" && fd.returnType == IntegerType && args.size <= 1
    case _ => false
  }

  val qmarkContext = TVarFactory.newContext

  def isQMarkId(id: Identifier) = TVarFactory.isTemp(id, qmarkContext)

  def tmplFunction(paramTypes: Seq[TypeTree]) = {
    val lambdaType = FunctionType(paramTypes, BooleanType)
    val paramid = FreshIdentifier("lamb", lambdaType)
    new FunDef(FreshIdentifier("tmpl", BooleanType), Seq(), Seq(ValDef(paramid)), BooleanType)
  }

  /**
   * Repackages '?' mark expression into tmpl functions
   */
  var qmarkCounter = 0 // used to generate unique ids for qmarks so that they can be extracted later
  def getQmarkCounter = {
    qmarkCounter += 1
    qmarkCounter
  }

  def qmarksToTmplFunction(ine: Expr) = {
    var tempIds = Seq[Identifier]()
    var indexToId = Map[BigInt, Identifier]()
    val lambBody = simplePostTransform {
      case q @ FunctionInvocation(_, Seq()) if isQMark(q) => // question mark with zero args
        val freshid = TVarFactory.createTemp("q" + getQmarkCounter, IntegerType, qmarkContext)
        tempIds :+= freshid
        freshid.toVariable

      case q @ FunctionInvocation(_, Seq(InfiniteIntegerLiteral(index))) if isQMark(q) => //question mark with one arg
        indexToId.getOrElse(index, {
          val freshid = TVarFactory.createTemp("q" + getQmarkCounter + "-" + index, IntegerType, qmarkContext)
          tempIds :+= freshid
          indexToId += (index -> freshid)
          freshid
        }).toVariable

      case other => other
    }(ine)
    FunctionInvocation(TypedFunDef(tmplFunction(tempIds.map(_.getType)), Seq()),
      Seq(Lambda(tempIds.map(id => ValDef(id)), lambBody)))
  }

  /*def qmarksToTmplFunction(ine: Expr) = {
    var tempIds = Seq[Identifier]()
    var indexToId = Map[BigInt, Identifier]()
    val lambBody = simplePostTransform {
      case q @ FunctionInvocation(_, Seq()) if isQMark(q) => // question mark with zero args
        val freshid = TemplateIdFactory.freshIdentifier("q")
        tempIds :+= freshid
        freshid.toVariable

      case q @ FunctionInvocation(_, Seq(InfiniteIntegerLiteral(index))) if isQMark(q) => //question mark with one arg
        indexToId.getOrElse(index, {
          val freshid = TemplateIdFactory.freshIdentifier("q" + index)
          tempIds :+= freshid
          indexToId += (index -> freshid)
          freshid
        }).toVariable

      case other => other
    }(ine)
    FunctionInvocation(TypedFunDef(tmplFunction(tempIds.map(_.getType)), Seq()),
      Seq(Lambda(tempIds.map(id => ValDef(id)), lambBody)))
  }*/

  /**
   * We do not support mixing of tmpl exprs and '?'.
   * TODO: Need to check that tmpl functions are not nested.
   */
  def tmplAndPost(fd: FunDef): (Option[Expr], Option[FunctionInvocation]) = {
    if (fd.postcondition.isDefined) {
      val Lambda(_, postBody) = fd.postcondition.get
      // collect all terms with question marks and convert them to a template
      val postWoQmarks = simplifyByConstructors(postBody) match {
        case And(args) if args.exists(exists(isQMark)) =>
          val (tempExprs, otherPreds) = args.partition(exists(isQMark))
          //println(s"Otherpreds: $otherPreds ${qmarksToTmplFunction(createAnd(tempExprs))}")
          createAnd(otherPreds :+ qmarksToTmplFunction(createAnd(tempExprs)))
        case pb if exists(isQMark)(pb) =>
          pb match {
            case l: Let =>
              val (letsCons, letsBody) = letStarUnapplyWithSimplify(l) // we try to see if the post is let* .. in e_1 ^ e_2 ^ ...
              letsBody match {
                case And(args) =>
                  val (tempExprs, rest) = args.partition(exists(isQMark))
                  val toTmplFun = qmarksToTmplFunction(letsCons(createAnd(tempExprs)))
                  createAnd(Seq(letsCons(createAnd(rest)), toTmplFun))
                case _ =>
                  qmarksToTmplFunction(pb)
              }
            case _ => qmarksToTmplFunction(pb)
          }
        case other => other
      }
      //the 'body' could be a template or 'And(pred, template)' or 'let ... and(...)'
      postWoQmarks match {
        case e if exists(isTemplateInvocation)(e) => e match {
          case finv @ FunctionInvocation(_, args) if isTemplateInvocation(finv) =>
            (None, Some(finv))
          case And(args) =>
            val (tempFuns, otherPreds) = args.partition(isTemplateInvocation)
            if (tempFuns.size > 1) {
              throw new IllegalStateException("Multiple template functions used in the postcondition: " + postBody)
            } else {
              val rest = if (otherPreds.size <= 1) otherPreds(0) else And(otherPreds)
              (Some(rest), Some(tempFuns(0).asInstanceOf[FunctionInvocation]))
            }
          case l: Let =>
            val (letsCons, letsBody) = letStarUnapplyWithSimplify(l)
            letsBody match {
              case And(args) =>
                val (tempFuns, rest) = args.partition(exists(isTemplateInvocation))
                if (tempFuns.size > 1) {
                  throw new IllegalStateException("Multiple template functions used in the postcondition: " + postBody)
                }
                val FunctionInvocation(tfd, Seq(Lambda(tids, body))) = tempFuns.head
                (Some(letsCons(createAnd(rest))), Some(FunctionInvocation(tfd, Seq(Lambda(tids, letsCons(body))))))
              case finv @ FunctionInvocation(tfd, Seq(Lambda(tids, body))) if isTemplateInvocation(finv) =>
                (None, Some(FunctionInvocation(tfd, Seq(Lambda(tids, letsCons(body))))))
            }
        }
        case pb =>
          (Some(pb), None)
      }
    } else {
      (None, None)
    }
  }

  class FunctionInfo(fd: FunDef) {
    //flags
    lazy val isTheoryOperation = fd.annotations.contains("theoryop")
    lazy val isMonotonic = fd.annotations.contains("monotonic")
    lazy val isCommutative = fd.annotations.contains("commutative")
    lazy val isDistributive = fd.annotations.contains("distributive")
    lazy val compose = fd.annotations.contains("compose")
    lazy val isLibrary = fd.annotations.contains("library")
    lazy val isExtern = fd.annotations.contains("extern")
    lazy val isBodyVisible = !fd.annotations.contains("invisibleBody")
    lazy val hasFieldFlag = fd.flags.contains(IsField(false))
    lazy val hasLazyFieldFlag = fd.flags.contains(IsField(true))
    lazy val isUserFunction = !hasFieldFlag && !hasLazyFieldFlag
    lazy val usePost = fd.annotations.contains("usePost")

    def extractTemplateFromLambda(tempLambda: Lambda): Expr = {
      val Lambda(vdefs, body) = tempLambda
      val vars = vdefs.map(_.id.toVariable)
      val tempVars = vars.map { // reuse template variables if possible
        case v if TemplateIdFactory.IsTemplateIdentifier(v.id) => v
        case v =>
          TemplateIdFactory.freshIdentifier(v.id.name).toVariable
      }
      val repmap = (vars zip tempVars).toMap[Expr, Expr]
      replace(repmap, body)
    }

    lazy val (post, templateExpr) = tmplAndPost(fd)
    lazy val postWoTemplate = post
    lazy val template = templateExpr map (finv => extractTemplateFromLambda(finv.args(0).asInstanceOf[Lambda]))
    lazy val normalizedTemplate = {
      template.map(normalizeExpr(_, (e1: Expr, e2: Expr) => throw new IllegalStateException("Not implemented yet!")))
    }

    def hasTemplate: Boolean = templateExpr.isDefined
    def getPostWoTemplate = postWoTemplate match {
      case None       => tru
      case Some(expr) => expr
    }
    def getTemplate = template.get
  }

  // a cache for function infos
  private var functionInfos = Map[FunDef, FunctionInfo]()
  implicit def funDefToFunctionInfo(fd: FunDef): FunctionInfo = {
    functionInfos.getOrElse(fd, {
      val info = new FunctionInfo(fd)
      functionInfos += (fd -> info)
      info
    })
  }
}
