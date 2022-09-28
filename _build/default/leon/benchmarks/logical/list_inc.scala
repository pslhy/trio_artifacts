import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class NatList
case class Cons(head: Nat, tail: NatList) extends NatList
case object Nil extends NatList
  
def list_map(xs: NatList, f: (Nat) => Nat): NatList =
  xs match {
    case Nil              => Nil
    case Cons(head, tail) => Cons (f(head), list_map(tail,f))
  }
  
def list_inc(xs: NatList): NatList = { choose { (out:NatList) =>

    def len(xs: NatList): Int =
      xs match {
        case Nil => 0
        case Cons(h,t) => 1+(len(t))
      }

    def nat_to_int(x: Nat): Int =
      x match {
        case Z => 0
        case S(m) => nat_to_int(m) + 1
      }

    def sum(xs: NatList) : Int =
      xs match {
        case Nil => 0
        case Cons(h,t) => nat_to_int(h)+sum(t)
      }

    len(xs)+sum(xs)==sum(out)

} }

}