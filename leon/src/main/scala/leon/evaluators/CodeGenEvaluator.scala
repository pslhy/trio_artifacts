/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._

import codegen.CompilationUnit
import codegen.CompiledExpression
import codegen.CodeGenParams

import leon.codegen.runtime.LeonCodeGenRuntimeException
import leon.codegen.runtime.LeonCodeGenEvaluationException

class CodeGenEvaluator(ctx: LeonContext, val unit: CompilationUnit) extends Evaluator(ctx, unit.program) with DeterministicEvaluator {

  val name = "codegen-eval"
  val description = "Evaluator for PureScala expressions based on compilation to JVM"

  val bank = unit.bank

  /** Another constructor to make it look more like other `Evaluator`s. */
  def this(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank, params: CodeGenParams = CodeGenParams.default) {
    this(ctx, new CompilationUnit(ctx, prog, bank, params))
  }

  private def compileExpr(expression: Expr, args: Seq[Identifier]): Option[CompiledExpression] = {
    ctx.timers.evaluators.codegen.compilation.start()
    try {
      Some(unit.compileExpression(expression, args)(ctx))
    } catch {
      case t: Throwable =>
        ctx.reporter.warning(expression.getPos, "Error while compiling expression: "+t.getMessage)
        None
    } finally {
      ctx.timers.evaluators.codegen.compilation.stop()
    }
  }

  def eval(expression: Expr, model: solvers.Model) : EvaluationResult = {
    compile(expression, model.toSeq.map(_._1)).map { e =>
      ctx.timers.evaluators.codegen.runtime.start()
      val res = e(model)
      ctx.timers.evaluators.codegen.runtime.stop()
      res
    }.getOrElse(EvaluationResults.EvaluatorError(s"Couldn't compile expression $expression"))
  }

  override def compile(expression: Expr, args: Seq[Identifier]) : Option[solvers.Model=>EvaluationResult] = {
    compileExpr(expression, args).map(ce => (model: solvers.Model) => {
        if (args.exists(arg => !model.isDefinedAt(arg))) {
          EvaluationResults.EvaluatorError("Model undefined for free arguments")
        } else try {
          EvaluationResults.Successful(ce.eval(model))
        } catch {
          case e : ArithmeticException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : ArrayIndexOutOfBoundsException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : LeonCodeGenRuntimeException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : LeonCodeGenEvaluationException =>
            EvaluationResults.EvaluatorError(e.getMessage)

          case e : java.lang.ExceptionInInitializerError =>
            EvaluationResults.RuntimeError(e.getException.getMessage)

          case so : java.lang.StackOverflowError =>
            EvaluationResults.RuntimeError("Stack overflow")
        }
      })
    }
  }
