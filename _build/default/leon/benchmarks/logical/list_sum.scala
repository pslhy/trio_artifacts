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
  
def list_fold(f: (Nat,Nat) => Nat, acc: Nat, xs: NatList): Nat =
  xs match {
    case Nil              => acc
    case Cons(head, tail) => f (list_fold(f, acc, tail), head)
  }
  
def nat_add(n1: Nat, n2: Nat): Nat =
  n1 match {
    case Z    => n2
    case S(m) => S (nat_add(m, n2))
  }
  
def list_sum(xs: NatList): Nat = { choose { (out:Nat) => 

   xs match {
     case Nil => out == Z
     case Cons(h,t) =>
       t match {
         case Nil => out == h
         case Cons(h2,t2) =>
           t2 match {
             case Nil => out == nat_add(h,h2)
             case Cons(h3,t3) => true
           }
       }
   }

} }

}