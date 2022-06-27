import leon.collection._
import leon.lang._
import leon.annotation._

import scala.language.postfixOps

object Termination {

  case class Task(tick: BigInt) {
    require(tick >= 0)
  }

  case class Core(tasks: Task, current: Option[BigInt]) 


  def insertBack(): Core = Core(Task(0), None())


  def looping(c: Core): Core = {
    c.current match {
      case Some(_) => looping(c)
      case None() => insertBack()
    }
  }

  @ignore
  def main(args: Array[String]) {
    looping(Core(Task(0), Some(0)))
  }

}
